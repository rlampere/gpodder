# -*- coding: utf-8 -*-
#RobL--v manual_entry.py is a new gPodder module added by RobL & created by ChatGPT
"""
Manual podcast/episode add + edit support for gPodder GTK.

This module is intentionally self-contained so the bulk of the code can live
outside of the existing gPodder source files. It creates its GTK dialogs in
Python, adds synthetic podcast URLs / episode GUIDs where gPodder requires
non-null unique values, copies a user-selected media file into gPodder's
managed download folder, and marks the created episode as downloaded.

Added in this version:
    * Batch import of episode media files into a selected podcast
    * File metadata import using Mutagen when available
      - comments/comment/description tag -> episode description
      - title tag -> episode title
      - file modified timestamp -> published date

Expected minimal integration points in gpodder/src/gpodder/gtkui/main.py:

    from .manual_entry import ManualEntryController

    # in new(), before self.create_actions()
    self.manual_entry_controller = ManualEntryController(self)

    # in create_actions(), after action group `g` is created
    self.manual_entry_controller.install_actions(g)

Expected menu additions in share/gpodder/ui/gtk/menus.ui:

    <item>
      <attribute name="action">win.manualAddPodcast</attribute>
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
      <attribute name="action">win.manualAddEpisodeBatch</attribute>
      <attribute name="label" translatable="yes">Add episode batch manually</attribute>
    </item>

    <item>
      <attribute name="action">win.manualEditEpisode</attribute>
      <attribute name="label" translatable="yes">Edit selected episode</attribute>
    </item>
"""

import datetime as _dt
import hashlib
import logging
import mimetypes
import os
import pathlib
import re
import shutil
import time
import uuid

import gpodder
from gpodder import util
from gpodder.gtkui.desktop import channel
from gpodder.model import Model

try:
    from mutagen import File as MutagenFile
    from mutagen import MutagenError
except Exception:  # pragma: no cover - optional dependency
    MutagenFile = None
    class MutagenError(Exception):
        pass

import gi  # isort:skip

gi.require_version('Gtk', '3.0')  # isort:skip
from gi.repository import Gio, Gtk  # isort:skip

_ = gpodder.gettext

logger = logging.getLogger(__name__)


class ManualEntryError(Exception):
    pass

#RobL--v
def _episode_edit_description(episode):
    """Return the description text to show in the manual episode editor.

    Prefer description_html because feed-imported episodes may store the
    publisher's original description there. If no HTML description exists,
    fall back to the plain-text description.
    """
    if episode is None:
        return ''

    if episode.description_html:
        return episode.description_html

    if episode.description:
        return episode.description

    return ''

def _episode_edit_description_is_html(episode):
    """Return True if the manual episode editor should save description as HTML."""
    return bool(episode is not None and episode.description_html)
#RobL--^

def _slugify(value):
    value = (value or '').strip().lower()
    value = re.sub(r'[^a-z0-9]+', '-', value)
    value = value.strip('-')
    return value or 'item'

def _stringify_tag_value(value):
    if value is None:
        return ''

    # Mutagen ID3 frame objects usually expose text as a list
    if hasattr(value, 'text'):
        text_value = getattr(value, 'text', None)
        if text_value:
            if isinstance(text_value, (list, tuple)):
                parts = [str(v).strip() for v in text_value if str(v).strip()]
                return '\n'.join(parts).strip()
            return str(text_value).strip()

    if isinstance(value, (list, tuple)):
        parts = [str(v).strip() for v in value if str(v).strip()]
        return '\n'.join(parts).strip()

    return str(value).strip()

def _get_tag_value(audio, *keys):
    if audio is None:
        return ''

    tags = getattr(audio, 'tags', None)
    if tags is None:
        return ''

    # Exact case-insensitive match first
    lowered = {str(k).lower(): k for k in tags.keys()} if hasattr(tags, 'keys') else {}
    for key in keys:
        actual = lowered.get(key.lower())
        if actual is not None:
            value = _stringify_tag_value(tags.get(actual))
            if value:
                return value

    # Prefix match for ID3 frames like COMM::eng
    if hasattr(tags, 'keys'):
        for actual_key in tags.keys():
            actual_key_str = str(actual_key).lower()
            for key in keys:
                if actual_key_str.startswith(key.lower()):
                    value = _stringify_tag_value(tags.get(actual_key))
                    if value:
                        return value

    return ''

def _extract_media_metadata(path_obj):
    source = pathlib.Path(path_obj).expanduser().resolve()
    title = source.stem
    description = ''
    published = int(source.stat().st_mtime)

    #print('MutagenFile =', MutagenFile)

    if MutagenFile is not None:
        audio_easy = None
        audio_raw = None

        try:
            audio_easy = MutagenFile(str(source), easy=True)
        except (MutagenError, OSError, ValueError, TypeError):
            audio_easy = None

        try:
            audio_raw = MutagenFile(str(source))
        except (MutagenError, OSError, ValueError, TypeError):
            audio_raw = None

        # Title
        tag_title = _get_tag_value(audio_easy, 'title')
        if not tag_title:
            tag_title = _get_tag_value(audio_raw, 'TIT2', 'title', 'tit2', '©nam')
        if tag_title:
            title = tag_title

        # Comments / description
        tag_description = _get_tag_value(audio_easy, 'comment', 'comments', 'description')
        if not tag_description:
            tag_description = _get_tag_value(
                audio_raw,
                'COMM', 'comment', 'comments',
                'TDES', 'description', 'desc',
                '©cmt'
            )
        if tag_description:
            description = tag_description

    return {
        'title': title.strip() or source.stem,
        'description': description.strip(),
        'published': published,
        'media_file': str(source),
    }

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
        self.set_default_size(720, 600)

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

        # Check if a podcast was selected or if the "All episodes" list was selected.
        if podcast is not None:
            self.entry_title.set_text(podcast.title or '')
            self.entry_link.set_text(podcast.link or '')
            self.entry_section.set_text(getattr(podcast, 'section', '') or _('Other'))
            buf = self.text_description.get_buffer()
            buf.set_text((podcast.description or '').strip())
            self.show_all()
        else:
            logger.warning('No podcast selected -or- [All episodes] was selected...cannot edit podcast entry.')

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
        self.set_resizable(True)
        self.set_default_size(760, 680)

        self._podcasts = list(podcasts)

        area = self.get_content_area()
        area.set_hexpand(True)
        area.set_vexpand(True)

        grid = Gtk.Grid(column_spacing=12, row_spacing=8, margin=12)
        grid.set_hexpand(True)
        grid.set_vexpand(True)
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
        self.file_media.set_hexpand(True)
        self.file_media.connect('selection-changed', self.on_media_file_selected)

        self.media_help_label = Gtk.Label(
            label=_('Select a media file first so the title, description, and published date fields can be populated.'),
            xalign=0,
        )
        self.media_help_label.set_line_wrap(True)
        self.media_help_label.set_max_width_chars(60)

        self.entry_link = Gtk.Entry()
        self.entry_link.set_placeholder_text('https://example.com/episode-page')
        self.entry_guid = Gtk.Entry()
        self.entry_guid.set_placeholder_text(_('Leave blank to auto-generate'))
        self.entry_published = Gtk.Entry()
        self.entry_published.set_text(_dt.datetime.now().strftime('%Y-%m-%d %H:%M'))
        self.spin_season_num = Gtk.SpinButton.new_with_range(0, 9999, 1)
        self.spin_episode_num = Gtk.SpinButton.new_with_range(0, 9999, 1)

        self.check_mark_new = Gtk.CheckButton.new_with_label(_('Mark episode as new'))
        self.check_mark_new.set_active(True)

        self.check_description_html = Gtk.CheckButton.new_with_label(_('Store description as HTML'))
        self.check_description_html.set_tooltip_text(
            _('Save the description field as HTML instead of plain text.')
        )
        self.check_replace_media = Gtk.CheckButton.new_with_label(_('Replace media file from selected source'))
        self.check_replace_media.set_active(not is_edit)

        self.text_description = Gtk.TextView(wrap_mode=Gtk.WrapMode.WORD)
        self.text_description.set_hexpand(True)
        self.text_description.set_vexpand(True)

        desc_sw = Gtk.ScrolledWindow()
        desc_sw.set_hexpand(True)
        desc_sw.set_vexpand(True)
        desc_sw.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        desc_sw.set_min_content_height(300)
        desc_sw.add(self.text_description)

        # Populate the form with the data fields.
        row = 0

        grid.attach(Gtk.Label(label=_('Podcast'), xalign=0), 0, row, 1, 1)
        grid.attach(self.combo_podcast, 1, row, 1, 1)
        row += 1

        # Add fields associated with the media file.
        grid.attach(Gtk.Label(label=_(''), xalign=0), 0, row, 1, 1)
        grid.attach(self.media_help_label, 1, row, 1, 1)
        row += 1

        grid.attach(Gtk.Label(label=_('Media file'), xalign=0), 0, row, 1, 1)
        grid.attach(self.file_media, 1, row, 1, 1)
        row += 1

        if is_edit:
            grid.attach(Gtk.Label(label=_('Current media file'), xalign=0), 0, row, 1, 1)
            curr_file = Gtk.Label(
                label=_('{}').format(getattr(episode, 'download_filename', '') or _('(none)')),
                xalign=0,
            )
            grid.attach(curr_file, 1, row, 1, 1)
            row += 1
            grid.attach(self.check_replace_media, 1, row, 1, 1)
            row += 1

        # Add remaining data fields.
        fields = [
            (_('Episode title'), self.entry_title),
            (_('Description'), desc_sw),
            (_('Published'), self.entry_published),
            (_('Episode page link'), self.entry_link),
            (_('Season'), self.spin_season_num),
            (_('Episode #'), self.spin_episode_num),
            (_('GUID override'), self.entry_guid),
        ]

        for label, widget in fields:
            if label:
                lbl = Gtk.Label(label=label, xalign=0)
                if label == _('Description'):
                    lbl.set_valign(Gtk.Align.START)
                    widget.set_vexpand(True)
                grid.attach(lbl, 0, row, 1, 1)
            else:
                spacer = Gtk.Label(label='', xalign=0)
                grid.attach(spacer, 0, row, 1, 1)
            grid.attach(widget, 1, row, 1, 1)
            row += 1

        grid.attach(self.check_mark_new, 1, row, 1, 1)
        row += 1
        grid.attach(self.check_description_html, 1, row, 1, 1)

        # Populate form fields if editing an existing episode.
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
            self.check_description_html.set_active(_episode_edit_description_is_html(episode))
            buf = self.text_description.get_buffer()
            buf.set_text(_episode_edit_description(episode).strip())

        self.show_all()

    def get_selected_podcast(self):
        idx = self.combo_podcast.get_active()
        return None if idx < 0 else self._podcasts[idx]

    def on_media_file_selected(self, chooser):
        filename = chooser.get_filename()
        if not filename:
            return

        metadata = _extract_media_metadata(filename)
        #print('TITLE =', repr(metadata.get('title')))
        #print('DESCRIPTION =', repr(metadata.get('description')))
        #print('PUBLISHED =', repr(metadata.get('published')))

        self.entry_title.set_text(metadata.get('title', '') or '')

        buf = self.text_description.get_buffer()
        buf.set_text(metadata.get('description', '') or '')

        published = metadata.get('published')
        if published:
            self.entry_published.set_text(
                _dt.datetime.fromtimestamp(int(published)).strftime('%Y-%m-%d %H:%M')
            )

    def get_data(self):
        buf = self.text_description.get_buffer()
        return {
            'podcast': self.get_selected_podcast(),
            'title': self.entry_title.get_text().strip(),
            'media_file': self.file_media.get_filename(),
            'replace_media': self.check_replace_media.get_active(),
            'published_text': self.entry_published.get_text().strip(),
            'link': self.entry_link.get_text().strip(),
            'guid': self.entry_guid.get_text().strip(),
            'season_num': self.spin_season_num.get_value_as_int(),
            'episode_num': self.spin_episode_num.get_value_as_int(),
            'is_new': self.check_mark_new.get_active(),
            'description': buf.get_text(buf.get_start_iter(), buf.get_end_iter(), True).strip(),
            'description_is_html': self.check_description_html.get_active(),
        }


class ManualBatchEpisodeDialog(Gtk.Dialog):
    def __init__(self, parent, podcasts, active_podcast=None):
        super().__init__(
            title=_('Add episode batch manually'),
            transient_for=parent,
            modal=True,
        )
        self.add_buttons(
            _('_Cancel'), Gtk.ResponseType.CANCEL,
            _('_Add'), Gtk.ResponseType.OK,
        )
        self.set_default_response(Gtk.ResponseType.OK)
        self.set_border_width(12)
        self.set_default_size(720, 420)

        self._podcasts = list(podcasts)

        area = self.get_content_area()
        grid = Gtk.Grid(column_spacing=12, row_spacing=8, margin=12)
        area.add(grid)

        self.combo_podcast = Gtk.ComboBoxText()
        active_index = 0
        for i, podcast in enumerate(self._podcasts):
            self.combo_podcast.append(str(i), podcast.title or podcast.url)
            if active_podcast is not None and podcast.url == active_podcast.url:
                active_index = i
        if self._podcasts:
            self.combo_podcast.set_active(active_index)

        self.selected_files = []

        self.file_batch = Gtk.Button.new_with_label(_('Select media files...'))
        self.file_batch.set_hexpand(True)
        self.file_batch.connect('clicked', self.on_choose_batch_files_clicked)
        self.file_batch_status = Gtk.Label(label=_('No files selected'), xalign=0)

        self.check_mark_new = Gtk.CheckButton.new_with_label(_('Mark imported episodes as new'))
        self.check_mark_new.set_active(True)
        self.check_use_tags = Gtk.CheckButton.new_with_label(_('Read title/comments from file tags when available'))
        self.check_use_tags.set_active(True)

        info = Gtk.Label(
            label=_(
                'Batch Import Rules:\n'
                ' • episode title = file [title] tag (if title tag is missing, filename is used.)\n'
                ' • episode description = file [comments/comment/description] tag\n'
                ' • episode published date = file modified date'
            ),
            xalign=0,
            justify=Gtk.Justification.LEFT,
        )

        row = 0

        for label, widget in (
            (_('Podcast'), self.combo_podcast),
            (_('Media files'), self.file_batch),
        ):
            lbl = Gtk.Label(label=label, xalign=0)
            grid.attach(lbl, 0, row, 1, 1)
            grid.attach(widget, 1, row, 1, 1)
            row += 1

        grid.attach(Gtk.Label(label='', xalign=0), 0, row, 1, 1)
        grid.attach(self.file_batch_status, 1, row, 1, 1)
        row += 1

        grid.attach(self.check_mark_new, 1, row, 1, 1)
        row += 1
        grid.attach(self.check_use_tags, 1, row, 1, 1)
        row += 1
        grid.attach(info, 1, row, 1, 1)

        self.show_all()

    def on_choose_batch_files_clicked(self, button):
        dialog = Gtk.FileChooserDialog(
            title=_('Select media files'),
            transient_for=self,
            action=Gtk.FileChooserAction.OPEN,
        )
        dialog.add_buttons(
            _('_Cancel'), Gtk.ResponseType.CANCEL,
            _('_Open'), Gtk.ResponseType.OK,
        )
        dialog.set_current_folder(gpodder.downloads)
        dialog.set_select_multiple(True)

        try:
            response = dialog.run()
            if response == Gtk.ResponseType.OK:
                self.selected_files = dialog.get_filenames()
                count = len(self.selected_files)
                if count == 0:
                    self.file_batch_status.set_text(_('No files selected'))
                elif count == 1:
                    self.file_batch_status.set_text(
                        _('1 file selected: %s') % os.path.basename(self.selected_files[0])
                    )
                else:
                    self.file_batch_status.set_text(
                        _('%d files selected') % count
                    )
        finally:
            dialog.destroy()

    def get_selected_podcast(self):
        idx = self.combo_podcast.get_active()
        return None if idx < 0 else self._podcasts[idx]

    def get_data(self):
        return {
            'podcast': self.get_selected_podcast(),
            'media_files': list(self.selected_files),
            'is_new': self.check_mark_new.get_active(),
            'use_file_tags': self.check_use_tags.get_active(),
        }


class ManualEntryController(object):
    """Glue object that can be attached to gPodder's main GTK window."""

    def __init__(self, ui):
        self.ui = ui

    def install_actions(self, action_group):
        for name, callback in (
            ('manualAddPodcast', self.on_manual_add_podcast_activate),
            ('manualEditPodcast', self.on_manual_edit_podcast_activate),
            ('manualAddEpisodeSelectedPodcast', self.on_manual_add_episode_activate),
            ('manualAddEpisodeBatchSelectedPodcast', self.on_manual_add_episode_batch_activate),
            ('manualEditEpisodeSelectedPodcast', self.on_manual_edit_episode_activate),
        ):
            action = Gio.SimpleAction.new(name, None)
            action.connect('activate', callback)
            action_group.add_action(action)

    def on_manual_add_podcast_activate(self, action, param=None):
        self.open_manual_add_podcast_dialog()

    def on_manual_edit_podcast_activate(self, action, param=None):
        self.open_manual_edit_podcast_dialog()

    def on_manual_add_episode_activate(self, action, param=None):
        self.open_manual_add_episode_dialog()

    def on_manual_add_episode_batch_activate(self, action, param=None):
        self.open_manual_add_episode_batch_dialog()

    def on_manual_edit_episode_activate(self, action, param=None):
        self.open_manual_edit_episode_dialog()

    def open_manual_add_podcast_dialog(self):
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

    def open_manual_edit_podcast_dialog(self):
        podcast = getattr(self.ui, 'active_channel', None)
        if podcast is None:
            self._show_error(
                _('No podcast selected'),
                _('Select a podcast first.')
            )
            return

        if getattr(podcast, 'ALL_EPISODES_PROXY', False):
            self._show_error(
                _('All Episodes list selected'),
                _('Select a real podcast first.')
            )
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

    def open_manual_add_episode_dialog(self):
        podcasts = list(self.ui.model.get_podcasts())
        if not podcasts:
            self._show_error(
                _('No podcasts available'),
                _('Create a podcast manually or subscribe to one first.'),
            )
            return

        active = getattr(self.ui, 'active_channel', None)
        dialog = ManualEpisodeDialog(self.ui.main_window, podcasts, active_podcast=active)
        try:
            response = dialog.run()
            if response == Gtk.ResponseType.OK:
                episode = self.add_manual_episode(**dialog.get_data())
                self._refresh_ui_after_episode_change(episode)
        except Exception as exc:
            self._show_error(_('Could not add episode manually'), str(exc))
        finally:
            dialog.destroy()

    def open_manual_add_episode_batch_dialog(self):
        podcasts = list(self.ui.model.get_podcasts())
        if not podcasts:
            self._show_error(
                _('No podcasts available'),
                _('Create a manual podcast or subscribe to one first.'),
            )
            return

        active = getattr(self.ui, 'active_channel', None)
        dialog = ManualBatchEpisodeDialog(self.ui.main_window, podcasts, active_podcast=active)
        try:
            response = dialog.run()
            if response == Gtk.ResponseType.OK:
                episodes = self.add_manual_episode_batch(**dialog.get_data())
                if episodes:
                    self._refresh_ui_after_episode_change(episodes[0])
        except Exception as exc:
            self._show_error(_('Could not add manual episode batch'), str(exc))
        finally:
            dialog.destroy()

    def open_manual_edit_episode_dialog(self):
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

    def add_manual_episode(self, podcast, title, media_file, published_text,
                           link='', guid='', season_num=0, episode_num=0,
                           is_new=True, description='', description_is_html=False,
                           replace_media=True):
        if podcast is None:
            raise ManualEntryError(_('A podcast must be selected.'))




        if not media_file:
            raise ManualEntryError(_('A media file must be selected.'))

        source = pathlib.Path(media_file).expanduser().resolve()
        if not source.exists() or not source.is_file():
            raise ManualEntryError(_('Selected media file was not found.'))

        metadata = _extract_media_metadata(source)

        title = (title or '').strip() or metadata['title']
        if not title:
            raise ManualEntryError(_('Episode title is required.'))

        if published_text:
            published = self._parse_published_datetime(published_text)
        else:
            published = metadata['published']

        description = (description or '').strip() or metadata['description']

        episode = podcast.EpisodeClass(podcast)
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
            description_is_html=description_is_html,
            media_source=source,
            replace_media=True,
            is_new_record=True,
        )

        episode.save()
        self._ensure_episode_in_channel_list(episode)
        if hasattr(podcast, '_determine_common_prefix'):
            podcast._determine_common_prefix()
        podcast.save()
        return episode

    def add_manual_episode_batch(self, podcast, media_files, is_new=True, use_file_tags=True):
        if podcast is None:
            raise ManualEntryError(_('A podcast must be selected.'))
        if not media_files:
            raise ManualEntryError(_('Select one or more media files.'))

        created = []
        for media_file in media_files:
            source = pathlib.Path(media_file).expanduser().resolve()
            if not source.exists() or not source.is_file():
                raise ManualEntryError(_('Selected media file was not found: {}').format(source))

            metadata = _extract_media_metadata(source) if use_file_tags else {
                'title': source.stem,
                'description': '',
                'published': int(source.stat().st_mtime),
                'media_file': str(source),
            }

            episode = podcast.EpisodeClass(podcast)
            self._apply_episode_fields(
                episode,
                podcast=podcast,
                title=metadata['title'],
                published=int(metadata['published']),
                link='',
                guid='',
                season_num=0,
                episode_num=0,
                is_new=is_new,
                description=metadata['description'],
                media_source=source,
                replace_media=True,
                is_new_record=True,
            )
            episode.save()
            self._ensure_episode_in_channel_list(episode)
            created.append(episode)

        if hasattr(podcast, '_determine_common_prefix'):
            podcast._determine_common_prefix()
        podcast.save()
        return created

    def update_manual_episode(self, episode, podcast, title, media_file, replace_media,
                              published_text, link='', guid='', season_num=0, episode_num=0,
                              is_new=True, description='', description_is_html=False):
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
            description_is_html=description_is_html,
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
                              description_is_html=False,
                              media_source=None, replace_media=False,
                              is_new_record=False):
        old_destination = None
        if getattr(episode, 'download_filename', None):
            old_destination = episode.local_filename(create=False, check_only=True)

        episode.title = title

        description = (description or '').strip()
        if description_is_html:
            episode.description = ''
            episode.description_html = description
        else:
            episode.description = description
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

    def _parse_published_datetime(self, text):
        text = (text or '').strip()
        if not text:
            return int(time.time())

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
