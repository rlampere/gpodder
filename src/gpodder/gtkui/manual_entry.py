# -*- coding: utf-8 -*-
#RobL--v manual_entry.py is a new gPodder module added by RobL & created by ChatGPT
"""
Manual podcast/episode add + edit support for gPodder GTK.

This module is intentionally self-contained so the bulk of the code can live
outside of the existing gPodder source files. It creates its GTK dialogs in
Python, adds synthetic podcast URLs / episode GUIDs where gPodder requires
non-null unique values, copies a user-selected media file into gPodder's
managed download folder, and marks the created episode as downloaded.

Expected minimal integration points in gpodder/src/gpodder/gtkui/main.py:

    from .manual_entry import ManualEntryController

    # in new(), before self.create_actions()
    self.manual_entry_controller = ManualEntryController(self)

    # in create_actions(), after action group `g` is created
    self.manual_entry_controller.install_actions(g)

Expected menu additions in share/gpodder/ui/gtk/menus.ui:

    <item>
      <attribute name="action">win.manualEntryManager</attribute>
      <attribute name="label" translatable="yes">Add podcast manually</attribute>
    </item>

    <item>
      <attribute name="action">win.manualEditPodcast</attribute>
      <attribute name="label" translatable="yes">Edit selected podcast</attribute>
    </item>

    <item>
      <attribute name="action">win.manualAddEpisode</attribute>
      <attribute name="label" translatable="yes">Add episode manually</attribute>
    </item>

    <item>
      <attribute name="action">win.manualEditEpisode</attribute>
      <attribute name="label" translatable="yes">Edit selected episode</attribute>
    </item>
"""

import datetime as _dt
import hashlib
import mimetypes
import os
import pathlib
import re
import shutil
import time
import uuid

import gpodder
from gpodder import util
from gpodder.model import Model

import gi  # isort:skip

gi.require_version('Gtk', '3.0')  # isort:skip
gi.require_version('Gst', '1.0')  # isort:skip
gi.require_version('GstPbutils', '1.0')  # isort:skip
from gi.repository import Gio, Gst, GstPbutils, Gtk  # isort:skip

_GST_TAGS_AVAILABLE = False
if gi.Repository.get_default().enumerate_versions('Gst') and gi.Repository.get_default().enumerate_versions('GstPbutils'):
    gi.require_version('Gst', '1.0')  # isort:skip
    gi.require_version('GstPbutils', '1.0')  # isort:skip
    from gi.repository import Gst, GstPbutils  # isort:skip
    Gst.init(None)
    _GST_TAGS_AVAILABLE = True

_GST_TAGS_AVAILABLE = False
_gst_versions = set(gi.Repository.get_default().enumerate_versions('Gst'))
_gst_pbutils_versions = set(gi.Repository.get_default().enumerate_versions('GstPbutils'))
if '1.0' in _gst_versions and '1.0' in _gst_pbutils_versions:
    gi.require_version('Gst', '1.0')  # isort:skip
    gi.require_version('GstPbutils', '1.0')  # isort:skip
    from gi.repository import Gst, GstPbutils  # isort:skip
    Gst.init(None)
    _GST_TAGS_AVAILABLE = True

_ = gpodder.gettext
Gst.init(None)


class ManualEntryError(Exception):
    pass


def _slugify(value):
    value = (value or '').strip().lower()
    value = re.sub(r'[^a-z0-9]+', '-', value)
    value = value.strip('-')
    return value or 'item'


class ManualPodcastDialog(Gtk.Dialog):
    def __init__(self, parent, podcast=None):
        self.podcast = podcast
        is_edit = podcast is not None
        super().__init__(
            title=_('Edit selected podcast') if is_edit else _('Add podcast manually'),
            transient_for=parent,
            modal=True,
        )
        self.add_buttons(
            _('_Cancel'), Gtk.ResponseType.CANCEL,
            _('_Save') if is_edit else _('_Add'), Gtk.ResponseType.OK,
        )
        self.set_default_response(Gtk.ResponseType.OK)
        self.set_border_width(12)
        self.set_default_size(560, 320)

        area = self.get_content_area()
        grid = Gtk.Grid(column_spacing=12, row_spacing=8, margin=12)
        area.add(grid)

        self.entry_title = Gtk.Entry()
        self.entry_title.set_activates_default(True)
        self.entry_link = Gtk.Entry()
        self.entry_link.set_placeholder_text('https://example.com')
        self.entry_section = Gtk.Entry()
        self.entry_section.set_text(_('Other'))
        self.text_description = Gtk.TextView(wrap_mode=Gtk.WrapMode.WORD)
        desc_sw = Gtk.ScrolledWindow()
        desc_sw.set_hexpand(True)
        desc_sw.set_vexpand(True)
        desc_sw.add(self.text_description)

        row = 0
        for label, widget in (
            (_('Title'), self.entry_title),
            (_('Website link'), self.entry_link),
            (_('Section'), self.entry_section),
        ):
            lbl = Gtk.Label(label=label, xalign=0)
            grid.attach(lbl, 0, row, 1, 1)
            grid.attach(widget, 1, row, 1, 1)
            row += 1

        lbl = Gtk.Label(label=_('Description'), xalign=0)
        grid.attach(lbl, 0, row, 1, 1)
        grid.attach(desc_sw, 1, row, 1, 1)

        if podcast is not None:
            self.entry_title.set_text(podcast.title or '')
            self.entry_link.set_text(podcast.link or '')
            self.entry_section.set_text(getattr(podcast, 'section', '') or _('Other'))
            buf = self.text_description.get_buffer()
            buf.set_text((podcast.description or '').strip())

        self.show_all()

    def get_data(self):
        buf = self.text_description.get_buffer()
        return {
            'title': self.entry_title.get_text().strip(),
            'link': self.entry_link.get_text().strip(),
            'section': self.entry_section.get_text().strip() or _('Other'),
            'description': buf.get_text(buf.get_start_iter(), buf.get_end_iter(), True).strip(),
        }


class ManualEpisodeDialog(Gtk.Dialog):
    def __init__(self, parent, podcasts, active_podcast=None, episode=None):
        self.episode = episode
        is_edit = episode is not None
        super().__init__(
            title=_('Edit selected episode') if is_edit else _('Add episode manually'),
            transient_for=parent,
            modal=True,
        )
        self.add_buttons(
            _('_Cancel'), Gtk.ResponseType.CANCEL,
            _('_Save') if is_edit else _('_Add'), Gtk.ResponseType.OK,
        )
        self.set_default_response(Gtk.ResponseType.OK)
        self.set_border_width(12)
        self.set_default_size(620, 460)

        self._podcasts = list(podcasts)

        area = self.get_content_area()
        grid = Gtk.Grid(column_spacing=12, row_spacing=8, margin=12)
        area.add(grid)

        self.combo_podcast = Gtk.ComboBoxText()
        active_index = 0
        target_podcast = episode.channel if episode is not None else active_podcast
        for i, podcast in enumerate(self._podcasts):
            self.combo_podcast.append(str(i), podcast.title or podcast.url)
            if target_podcast is not None and podcast.url == target_podcast.url:
                active_index = i
        if self._podcasts:
            self.combo_podcast.set_active(active_index)

        self.entry_title = Gtk.Entry()
        self.entry_title.set_activates_default(True)
        self.file_media = Gtk.FileChooserButton.new(_('Select media file'), Gtk.FileChooserAction.OPEN)
        self.file_media.set_select_multiple(True)
        self.file_media.set_hexpand(True)
        self.entry_link = Gtk.Entry()
        self.entry_link.set_placeholder_text('https://example.com/episode-page')
        self.entry_guid = Gtk.Entry()
        self.entry_guid.set_placeholder_text(_('Leave blank to auto-generate'))
        self.entry_published = Gtk.Entry()
        self.entry_published.set_text('')
        self.spin_season_num = Gtk.SpinButton.new_with_range(0, 9999, 1)
        self.spin_episode_num = Gtk.SpinButton.new_with_range(0, 9999, 1)
        self.check_mark_new = Gtk.CheckButton.new_with_label(_('Mark episode as new'))
        self.check_mark_new.set_active(True)
        self.check_replace_media = Gtk.CheckButton.new_with_label(_('Replace media file from selected source'))
        self.check_replace_media.set_active(not is_edit)
        self.text_description = Gtk.TextView(wrap_mode=Gtk.WrapMode.WORD)
        desc_sw = Gtk.ScrolledWindow()
        desc_sw.set_hexpand(True)
        desc_sw.set_vexpand(True)
        desc_sw.add(self.text_description)

        fields = [
            (_('Podcast'), self.combo_podcast),
            (_('Episode title'), self.entry_title),
            (_('Description'), desc_sw),
            (_('Published (YYYY-MM-DD HH:MM)'), self.entry_published),
            (_('Episode page link'), self.entry_link),
            (_('Season'), self.spin_season_num),
            (_('Episode #'), self.spin_episode_num),
            (_('GUID override'), self.entry_guid),
            (_('Media file'), self.file_media),
        ]

        row = 0
        for label, widget in fields:
            lbl = Gtk.Label(label=label, xalign=0)
            grid.attach(lbl, 0, row, 1, 1)
            grid.attach(widget, 1, row, 1, 1)
            row += 1

        if is_edit:
            media_label = Gtk.Label(
                label=_('Media file: {}').format(getattr(episode, 'download_filename', '') or _('(none)')),
                xalign=0,
            )
            grid.attach(media_label, 1, row, 1, 1)
            row += 1
            grid.attach(self.check_replace_media, 1, row, 1, 1)
            row += 1

        grid.attach(self.check_mark_new, 1, row, 1, 1)

        if episode is not None:
            self.entry_title.set_text(episode.title or '')
            if episode.published:
                self.entry_published.set_text(
                    _dt.datetime.fromtimestamp(int(episode.published)).strftime('%Y-%m-%d %H:%M')
                )
            self.entry_link.set_text(episode.link or '')
            self.entry_guid.set_text(episode.guid or '')
            self.spin_season_num.set_value(int(getattr(episode, 'season_num', 0) or 0))
            self.spin_episode_num.set_value(int(getattr(episode, 'episode_num', 0) or 0))
            self.check_mark_new.set_active(bool(getattr(episode, 'is_new', False)))
            self.check_replace_media.set_active(False)
            buf = self.text_description.get_buffer()
            buf.set_text((episode.description or '').strip())

        self.show_all()

    def get_selected_podcast(self):
        idx = self.combo_podcast.get_active()
        return None if idx < 0 else self._podcasts[idx]

    def get_data(self):
        buf = self.text_description.get_buffer()
        media_files = self.file_media.get_filenames()
        return {
            'podcast': self.get_selected_podcast(),
            'title': self.entry_title.get_text().strip(),
            'media_file': media_files[0] if media_files else None,
            'media_files': media_files,
            'replace_media': self.check_replace_media.get_active(),
            'published_text': self.entry_published.get_text().strip(),
            'link': self.entry_link.get_text().strip(),
            'guid': self.entry_guid.get_text().strip(),
            'season_num': self.spin_season_num.get_value_as_int(),
            'episode_num': self.spin_episode_num.get_value_as_int(),
            'is_new': self.check_mark_new.get_active(),
            'description': buf.get_text(buf.get_start_iter(), buf.get_end_iter(), True).strip(),
        }


class ManualEntryController(object):
    """Glue object that can be attached to gPodder's main GTK window."""

    def __init__(self, ui):
        self.ui = ui

    def install_actions(self, action_group):
        for name, callback in (
            ('manualEntryManager', self.on_manual_entry_manager_activate),
            ('manualEditPodcast', self.on_manual_edit_podcast_activate),
            ('manualAddEpisode', self.on_manual_add_episode_activate),
            ('manualEditEpisode', self.on_manual_edit_episode_activate),
        ):
            action = Gio.SimpleAction.new(name, None)
            action.connect('activate', callback)
            action_group.add_action(action)

    def on_manual_entry_manager_activate(self, action, param=None):
        self.open_manual_podcast_dialog()

    def on_manual_edit_podcast_activate(self, action, param=None):
        self.open_edit_manual_podcast_dialog()

    def on_manual_add_episode_activate(self, action, param=None):
        self.open_manual_episode_dialog()

    def on_manual_edit_episode_activate(self, action, param=None):
        self.open_edit_manual_episode_dialog()

    def open_manual_podcast_dialog(self):
        dialog = ManualPodcastDialog(self.ui.main_window)
        try:
            response = dialog.run()
            if response == Gtk.ResponseType.OK:
                podcast = self.create_manual_podcast(**dialog.get_data())
                self._refresh_ui_after_podcast_change(podcast, select=True)
        except Exception as exc:
            self._show_error(_('Could not create manual podcast'), str(exc))
        finally:
            dialog.destroy()

    def open_edit_manual_podcast_dialog(self):
        podcast = getattr(self.ui, 'active_channel', None)
        if podcast is None:
            self._show_error(_('No podcast selected'), _('Select a podcast first.'))
            return

        dialog = ManualPodcastDialog(self.ui.main_window, podcast=podcast)
        try:
            response = dialog.run()
            if response == Gtk.ResponseType.OK:
                podcast = self.update_manual_podcast(podcast, **dialog.get_data())
                self._refresh_ui_after_podcast_change(podcast, select=True)
        except Exception as exc:
            self._show_error(_('Could not update podcast'), str(exc))
        finally:
            dialog.destroy()

    def open_manual_episode_dialog(self):
        podcasts = list(self.ui.model.get_podcasts())
        if not podcasts:
            self._show_error(
                _('No podcasts available'),
                _('Create a manual podcast or subscribe to one first.'),
            )
            return

        active = getattr(self.ui, 'active_channel', None)
        dialog = ManualEpisodeDialog(self.ui.main_window, podcasts, active_podcast=active)
        try:
            response = dialog.run()
            if response == Gtk.ResponseType.OK:
                result = self.add_manual_episode(**dialog.get_data())
                self._refresh_ui_after_episode_change(result[-1] if isinstance(result, list) else result)
        except Exception as exc:
            self._show_error(_('Could not add manual episode'), str(exc))
        finally:
            dialog.destroy()

    def open_edit_manual_episode_dialog(self):
        episode = self._get_single_selected_episode()
        if episode is None:
            self._show_error(_('No episode selected'), _('Select exactly one episode first.'))
            return

        podcasts = list(self.ui.model.get_podcasts())
        dialog = ManualEpisodeDialog(self.ui.main_window, podcasts, episode=episode)
        try:
            response = dialog.run()
            if response == Gtk.ResponseType.OK:
                episode = self.update_manual_episode(episode, **dialog.get_data())
                self._refresh_ui_after_episode_change(episode)
        except Exception as exc:
            self._show_error(_('Could not update episode'), str(exc))
        finally:
            dialog.destroy()

    def create_manual_podcast(self, title, description='', link='', section=''):
        title = (title or '').strip()
        if not title:
            raise ManualEntryError(_('Podcast title is required.'))

        podcast = self.ui.model.PodcastClass(self.ui.model)
        podcast.url = self._build_unique_manual_podcast_url(title)
        podcast.title = title
        podcast.link = link.strip()
        podcast.description = description.strip()
        podcast.cover_url = None
        podcast.payment_url = None
        podcast.section = (section or '').strip() or _('Other')
        podcast.download_folder = None
        podcast.save()
        podcast.get_save_dir(force_new=True)
        podcast.save()
        return podcast

    def update_manual_podcast(self, podcast, title, description='', link='', section=''):
        title = (title or '').strip()
        if not title:
            raise ManualEntryError(_('Podcast title is required.'))

        old_title = podcast.title or ''
        podcast.link = link.strip()
        podcast.description = description.strip()
        podcast.section = (section or '').strip() or _('Other')

        if title != old_title:
            podcast.rename(title)
        else:
            podcast.title = title
            podcast.save()

        podcast.link = link.strip()
        podcast.description = description.strip()
        podcast.section = (section or '').strip() or _('Other')
        podcast.save()
        return podcast

    def add_manual_episode(self, podcast, title, media_files=None, published_text='',
                           media_file=None,
                           link='', guid='', season_num=0, episode_num=0,
                           is_new=True, description='', replace_media=True):
        if podcast is None:
            raise ManualEntryError(_('A podcast must be selected.'))

        files = [f for f in (media_files or []) if f]
        if media_file and media_file not in files:
            files.append(media_file)
        if not files:
            raise ManualEntryError(_('A media file must be selected.'))

        title = (title or '').strip()
        episodes = []
        for media_file in files:
            source = pathlib.Path(media_file).expanduser().resolve()
            if not source.exists() or not source.is_file():
                raise ManualEntryError(_('Selected media file was not found.'))

            metadata = self._read_media_metadata(source)
            episode_title = metadata.get('title') or title or source.stem
            episode_description = metadata.get('description') or (description or '').strip() or ''
            published = self._parse_published_datetime(published_text, metadata.get('published'))

            episode = podcast.EpisodeClass(podcast)
            self._apply_episode_fields(
                episode,
                podcast=podcast,
                title=episode_title,
                published=published,
                link=link,
                guid=guid,
                season_num=season_num,
                episode_num=episode_num,
                is_new=is_new,
                description=episode_description,
                media_source=source,
                replace_media=True,
                is_new_record=True,
            )

            episode.save()
            self._ensure_episode_in_channel_list(episode)
            episodes.append(episode)

        if hasattr(podcast, '_determine_common_prefix'):
            podcast._determine_common_prefix()
        podcast.save()
        return episodes if len(episodes) > 1 else episodes[0]

    def update_manual_episode(self, episode, podcast, title, media_file, replace_media,
                              published_text, link='', guid='', season_num=0, episode_num=0,
                              is_new=True, description=''):
        if podcast is None:
            raise ManualEntryError(_('A podcast must be selected.'))

        title = (title or '').strip()
        if not title:
            raise ManualEntryError(_('Episode title is required.'))

        source = None
        if replace_media:
            if not media_file:
                raise ManualEntryError(_('Select a media file or clear "Replace media file".'))
            source = pathlib.Path(media_file).expanduser().resolve()
            if not source.exists() or not source.is_file():
                raise ManualEntryError(_('Selected media file was not found.'))

        published = self._parse_published_datetime(published_text)
        old_podcast = episode.channel

        if podcast is not old_podcast:
            if episode in old_podcast.children:
                old_podcast.children.remove(episode)
            episode.channel = podcast
            episode.podcast_id = podcast.id

        self._apply_episode_fields(
            episode,
            podcast=podcast,
            title=title,
            published=published,
            link=link,
            guid=guid,
            season_num=season_num,
            episode_num=episode_num,
            is_new=is_new,
            description=description,
            media_source=source,
            replace_media=bool(replace_media),
            is_new_record=False,
        )

        episode.save()
        self._ensure_episode_in_channel_list(episode)
        if old_podcast is not podcast:
            old_podcast.save()
        if hasattr(podcast, '_determine_common_prefix'):
            podcast._determine_common_prefix()
        podcast.save()
        return episode

    def _apply_episode_fields(self, episode, podcast, title, published, link, guid,
                              season_num, episode_num, is_new, description,
                              media_source=None, replace_media=False,
                              is_new_record=False):
        old_destination = None
        if getattr(episode, 'download_filename', None):
            old_destination = episode.local_filename(create=False, check_only=True)

        episode.title = title
        episode.description = (description or '').strip()
        episode.description_html = ''
        if hasattr(episode, 'cache_text_description'):
            episode.cache_text_description()

        episode.guid = guid.strip() or episode.guid or self._build_manual_episode_guid(podcast, title)
        episode.link = link.strip() or (media_source.as_uri() if media_source is not None else episode.link)
        episode.published = published
        episode.payment_url = None
        episode.total_time = getattr(episode, 'total_time', 0) or 0
        episode.current_position = 0
        episode.current_position_updated = 0
        episode.last_playback = 0 if is_new else int(time.time())
        if hasattr(episode, 'season_num'):
            episode.season_num = int(season_num or 0)
        if hasattr(episode, 'episode_num'):
            episode.episode_num = int(episode_num or 0)

        if media_source is not None:
            episode.url = media_source.as_uri()
            episode.mime_type = mimetypes.guess_type(str(media_source))[0] or 'application/octet-stream'
            episode.file_size = media_source.stat().st_size
            destination = episode.local_filename(create=True, force_update=True, template=media_source.name)
            os.makedirs(podcast.save_dir, exist_ok=True)
            if os.path.abspath(destination) != os.path.abspath(str(media_source)):
                shutil.copy2(str(media_source), destination)
            episode.on_downloaded(destination)
            if old_destination and os.path.exists(old_destination) and os.path.abspath(old_destination) != os.path.abspath(destination):
                try:
                    os.remove(old_destination)
                except OSError:
                    pass
        else:
            if replace_media:
                raise ManualEntryError(_('A replacement media file is required.'))
            # Re-run naming logic if metadata changed and a managed file exists.
            if old_destination and os.path.exists(old_destination):
                destination = episode.local_filename(create=True, force_update=True)
                if old_destination != destination and os.path.exists(old_destination):
                    try:
                        os.remove(old_destination)
                    except OSError:
                        pass
                episode.file_size = os.path.getsize(destination) if os.path.exists(destination) else getattr(episode, 'file_size', 0)
                episode.state = gpodder.STATE_DOWNLOADED

        episode.is_new = bool(is_new)
        if not episode.is_new:
            episode.last_playback = int(time.time())

    def _ensure_episode_in_channel_list(self, episode):
        podcast = episode.channel
        if episode not in podcast.children:
            podcast.children.append(episode)
        podcast.children[:] = list(Model.sort_episodes_by_pubdate(podcast.children, reverse=True))

    def _build_unique_manual_podcast_url(self, title):
        slug = _slugify(title)
        existing = {pod.url for pod in self.ui.model.get_podcasts()}
        base = f'manual://podcast/{slug}'
        if base not in existing:
            return base
        suffix = 2
        while True:
            candidate = f'{base}-{suffix}'
            if candidate not in existing:
                return candidate
            suffix += 1

    def _build_manual_episode_guid(self, podcast, title):
        return 'manual://episode/{}/{}-{}'.format(
            _slugify(podcast.title or podcast.url),
            _slugify(title),
            uuid.uuid4().hex,
        )

    def _read_media_metadata(self, source):
        file = Gio.File.new_for_path(str(source))
        info = file.query_info(
            Gio.FILE_ATTRIBUTE_TIME_MODIFIED,
            Gio.FileQueryInfoFlags.NONE,
            None,
        )
        tags = None
        if _GST_TAGS_AVAILABLE:
            discoverer = GstPbutils.Discoverer.new(5 * Gst.SECOND)
            media_info = discoverer.discover_uri(source.as_uri())
            tags = media_info.get_tags() if media_info is not None else None

        title = self._get_tag_string(tags, 'title') or source.stem
        description = self._get_tag_string(tags, 'comment') or ''
        modified = info.get_attribute_uint64(Gio.FILE_ATTRIBUTE_TIME_MODIFIED)
        return {
            'title': (title or '').strip(),
            'description': (description or '').strip(),
            'published': int(modified) if modified else None,
        }

    def _get_tag_string(self, taglist, tag_name):
        if taglist is None:
            return None
        has_tag, value = taglist.get_string(tag_name)
        if has_tag:
            return value
        return None

    def _parse_published_datetime(self, text, fallback_timestamp=None):
        text = (text or '').strip()
        if not text:
            return int(fallback_timestamp) if fallback_timestamp else int(time.time())

        for fmt in ('%Y-%m-%d %H:%M', '%Y-%m-%d', '%Y/%m/%d %H:%M', '%Y/%m/%d'):
            try:
                dt = _dt.datetime.strptime(text, fmt)
                return int(dt.timestamp())
            except ValueError:
                pass

        raise ManualEntryError(
            _('Published date must use YYYY-MM-DD or YYYY-MM-DD HH:MM.')
        )

    def _get_single_selected_episode(self):
        getter = getattr(self.ui, 'get_selected_episodes', None)
        if getter is None:
            return None
        episodes = list(getter())
        if len(episodes) != 1:
            return None
        return episodes[0]

    def _refresh_ui_after_podcast_change(self, podcast, select=False):
        select_url = podcast.url if select else None
        self.ui.update_podcast_list_model(select_url=select_url)
        if getattr(self.ui, 'active_channel', None) and self.ui.active_channel.url == podcast.url:
            self.ui.update_episode_list_model()
            self.ui.update_episode_list_icons(update_all=True)

    def _refresh_ui_after_episode_change(self, episode):
        podcast = episode.channel
        if getattr(self.ui, 'active_channel', None) and self.ui.active_channel.url == podcast.url:
            self.ui.update_podcast_list_model(selected=True)
            self.ui.update_episode_list_model()
            self.ui.update_episode_list_icons(update_all=True)
        else:
            self.ui.update_podcast_list_model(select_url=podcast.url)

    def _show_error(self, title, message):
        dialog = Gtk.MessageDialog(
            transient_for=self.ui.main_window,
            modal=True,
            message_type=Gtk.MessageType.ERROR,
            buttons=Gtk.ButtonsType.CLOSE,
            text=title,
        )
        dialog.format_secondary_text(message)
        dialog.run()
        dialog.destroy()
