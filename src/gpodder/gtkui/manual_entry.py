# -*- coding: utf-8 -*-
#RobL-v-v-v-v-v-v-v-v-v-v-#-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-
# ---------------
# manual_entry.py
# ---------------
# This is a new module added for the gPodder+ project. This module is
# intentionally self-contained so the bulk of the code can live outside of
# the existing gPodder source files. The entirety of this module was added by
# Rob L. and all of the code (with a few minor exceptions) was auto-generated
# by ChatGPT.
#
# This module creates GTK dialogs in Python to:
#   1. Manually create new podcasts without using online sources
#   2. Manually update podcasts
#   3. Manually add individual episodes to an existing podcast
#   4. Manually add a batch of episodes to an existing podcast
#   5. Manually update an episode for a specific podcast
#   6. Search for and import podcast metadata from online sources
#   7. Extract metadata from local media files to create new episodes
#
#-------------------------------------------------------------------------------
# gPodder+ - An augmentation to and modification of the gPodder codebase
# Copyright (c) 2026 Rob L.
#
# gPodder+ is free software that applies the same GNU licensing and statements
# of non-warranty as the original gPodder codebase. It is a derivative work
# that builds on the original gPodder code, which is licensed under the GNU
# General Public License v3.0 or later. gPodder+ is not a separate software
# project and does not have its own license.#
#-------------------------------------------------------------------------------
# gPodder - A media aggregator and podcast client
# Copyright (c) 2005-2026 The gPodder Team
#
# gPodder is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3 of the License, or
# (at your option) any later version.
#
# gPodder is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program. If not, see <http://www.gnu.org/licenses/>.
#
#RobL-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-
#
import datetime as _dt
import hashlib
import html
import logging
import mimetypes
import os
import pathlib
import re
import shutil
import threading
import time
import uuid

import gpodder
from gpodder import util, podcastmetadata
from gpodder.gtkui.desktop import channel
from gpodder.model import Model

try:
    from mutagen import File as MutagenFile
    from mutagen import MutagenError
except Exception:  # pragma: no cover - optional dependency
    MutagenFile = None
    class MutagenError(Exception):
        pass

import gi

gi.require_version('Gtk', '3.0')
from gi.repository import Gio, GLib, Gtk, GdkPixbuf

from io import BytesIO

from urllib.parse import urlparse
from urllib.request import Request, urlopen
from urllib.error import URLError, HTTPError

# Text string processor for internationalization/localization.
_ = gpodder.gettext

# Plural-aware text string processor (1 egg, 2 eggs)
N_ = gpodder.ngettext

# Set up module-level logger.
logger = logging.getLogger(__name__)
#logger.setLevel(logging.INFO)

# Constant values used within this module.
DEFAULT_COL_SPACING = 14
DEFAULT_ROW_SPACING = 10
DEFAULT_MARGIN = 12

#===============================================================================
# Module-Level Helper Functions
#===============================================================================
def _ask_yes_no(parent, title, message):
    """Display a yes/no confirmation dialog and return True if the user clicks Yes."""
    dialog = Gtk.MessageDialog(
        transient_for=parent,
        modal=True,
        message_type=Gtk.MessageType.QUESTION,
        buttons=Gtk.ButtonsType.YES_NO,
        text=title,
    )

    dialog.format_secondary_text(message)

    response = dialog.run()
    dialog.destroy()

    return response == Gtk.ResponseType.YES

def _embedded_cover_art_to_pixbuf(image_data, size=96):
    """Convert embedded cover image bytes to a scaled GdkPixbuf."""

    if not image_data:
        return None

    loader = GdkPixbuf.PixbufLoader()
    loader.write(image_data)
    loader.close()

    pixbuf = loader.get_pixbuf()
    if pixbuf is None:
        return None

    return pixbuf.scale_simple(
        size,
        size,
        GdkPixbuf.InterpType.BILINEAR,
    )

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
    """Return True if the manual episode editor should save description as HTML.
       If False, description is saved as plain text."""
    return bool(episode is not None and episode.description_html)

def _extract_embedded_cover_art(path_obj):
    """Return embedded cover image bytes from an audio file, if present."""

    if MutagenFile is None:
        return None

    source = pathlib.Path(path_obj).expanduser().resolve()

    try:
        audio = MutagenFile(str(source))
    except (MutagenError, OSError, ValueError, TypeError):
        return None

    if audio is None:
        return None

    tags = getattr(audio, 'tags', None)
    if tags is None:
        return None

    # MP3 / ID3 APIC frames.
    try:
        for key in tags.keys():
            if str(key).startswith('APIC'):
                frame = tags[key]
                data = getattr(frame, 'data', None)
                if data:
                    return data
    except Exception:
        logger.debug('Could not read APIC embedded artwork from %s', source, exc_info=True)

    # MP4 / M4A cover art.
    try:
        covr = tags.get('covr')
        if covr:
            return bytes(covr[0])
    except Exception:
        logger.debug('Could not read MP4 embedded artwork from %s', source, exc_info=True)

    # FLAC/Vorbis pictures.
    try:
        pictures = getattr(audio, 'pictures', None)
        if pictures:
            data = getattr(pictures[0], 'data', None)
            if data:
                return data
    except Exception:
        logger.debug('Could not read FLAC embedded artwork from %s', source, exc_info=True)

    return None

def _extract_media_metadata(path_obj):
    """Extract podcast episode metadata from a media file using Mutagen, if available."""
    source = pathlib.Path(path_obj).expanduser().resolve()

    title = source.stem
    description = ''
    published = int(source.stat().st_mtime)
    link = ''
    guid = ''
    season_num = 0
    episode_num = 0
    total_time = 0

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

        # Duration
        try:
            info = getattr(audio_raw, 'info', None) or getattr(audio_easy, 'info', None)
            length = getattr(info, 'length', 0) or 0
            total_time = int(length)
        except Exception:
            total_time = 0

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

        # Published date
        tag_date = _get_tag_value(
            audio_easy,
            'date', 'year', 'originaldate', 'releasedate'
        )
        if not tag_date:
            tag_date = _get_tag_value(
                audio_raw,
                'TDRC', 'TYER', 'TDOR', 'TDAT', 'date', 'year', '©day'
            )

        tag_published = _parse_tag_date_to_timestamp(tag_date)
        if tag_published:
            published = tag_published

        # Episode page / website link
        tag_link = _get_tag_value(
            audio_easy,
            'website', 'url', 'podcasturl', 'episodeurl'
        )
        if not tag_link:
            tag_link = _get_tag_value(
                audio_raw,
                'WOAS', 'WXXX', 'website', 'url', 'podcasturl', 'episodeurl'
            )
        if tag_link:
            link = tag_link

        # GUID / unique identifier
        tag_guid = _get_tag_value(
            audio_easy,
            'guid', 'podcastguid', 'episodeguid'
        )
        if not tag_guid:
            tag_guid = _get_tag_value(
                audio_raw,
                'UFID', 'guid', 'podcastguid', 'episodeguid'
            )
        if tag_guid:
            guid = tag_guid

        # Season number, if present as a custom tag.
        tag_season = _get_tag_value(
            audio_easy,
            'season', 'seasonnumber', 'podcastseason'
        )
        if not tag_season:
            tag_season = _get_tag_value(
                audio_raw,
                'season', 'seasonnumber', 'podcastseason'
            )
        season_num = _parse_first_int(tag_season)

        # Episode number. Track number is a reasonable fallback for manually tagged files.
        tag_episode = _get_tag_value(
            audio_easy,
            'episode', 'episodenumber', 'podcastepisode', 'tracknumber'
        )
        if not tag_episode:
            tag_episode = _get_tag_value(
                audio_raw,
                'episode', 'episodenumber', 'podcastepisode', 'TRCK', 'tracknumber'
            )
        episode_num = _parse_first_int(tag_episode)

    return {
        'title': title.strip() or source.stem,
        'description': description.strip(),
        'published': published,
        'media_file': str(source),
        'link': link.strip(),
        'guid': guid.strip(),
        'season_num': season_num,
        'episode_num': episode_num,
        'total_time': total_time,
    }

def _get_tag_value(audio, *keys):
    """Return the value of the first matching tag key from the audio file's tags."""
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

def _is_url_reachable(url, timeout=10):
    """Return True if the URL is reachable (HTTP status 2xx or 3xx) or starts with [manual:].

       This helper function checks if a given URL is reachable by making a HEAD request
       with a timeout. If the URL starts with "manual:" or is reachable (returns a
       2xx or 3xx status code) return True."""
    url = (url or '').strip()

    if url.startswith("manual:"):
        return True

    parsed = urlparse(url)
    if parsed.scheme not in ('http', 'https') or not parsed.netloc:
        return False

    try:
        request = Request(
            url,
            headers={'User-Agent': 'gPodder+'}
        )

        with urlopen(request, timeout=timeout) as response:
            return 200 <= response.status < 400

    except (URLError, HTTPError, TimeoutError):
        return False

def _media_metadata_to_episode_metadata(metadata):
    """Convert local media file tags into the same object shape used by online metadata."""

    return podcastmetadata.MetadataEpisode(
        title=metadata.get('title') or '',
        url='',  # Do not populate Media URL from a local file.
        link=metadata.get('link') or '',
        description=metadata.get('description') or '',
        published=metadata.get('published') or 0,
        duration=metadata.get('total_time') or 0,
        image_url='',  # Embedded artwork is not a URL.
        season=metadata.get('season_num') or 0,
        number=metadata.get('episode_num') or 0,
        guid=metadata.get('guid') or '',
        source='mp3-tags',
        source_id=metadata.get('media_file') or '',
        raw=metadata,
    )

def _parse_first_int(value):
    value = (value or '').strip()
    if not value:
        return 0

    # Handles "12", "12/30", "S02E12", etc.
    match = re.search(r'\d+', value)
    return int(match.group(0)) if match else 0

def _parse_tag_date_to_timestamp(value):
    value = (value or '').strip()
    if not value:
        return 0

    # Common tag forms:
    #   2026
    #   2026-05-22
    #   2026-05-22 13:30
    #   2026-05-22T13:30:00
    value = value.replace('T', ' ').replace('Z', '').strip()

    for fmt in (
            '%Y-%m-%d %H:%M:%S',
            '%Y-%m-%d %H:%M',
            '%Y-%m-%d',
            '%Y'):
        try:
            dt = _dt.datetime.strptime(value[:len(_dt.datetime.now().strftime(fmt))], fmt)
            return int(dt.timestamp())
        except Exception:
            pass

    return 0

def _slugify(value):
    """Convert a string into a slug suitable for use in URLs or GUIDs.""" 
    value = (value or '').strip().lower()
    value = re.sub(r'[^a-z0-9]+', '-', value)
    value = value.strip('-')
    return value or 'item'

def _stringify_tag_value(value):
    """Convert a Mutagen tag value into a plain string for display."""
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

#===============================================================================
class ManualEntryError(Exception):
    pass

#===============================================================================
class ManualPodcastMetadataSearchDialog(Gtk.Dialog):
    """Search online podcast metadata providers and return one selected podcast."""

    COL_TITLE = 0
    COL_FEED_URL = 1
    COL_WEBSITE_URL = 2
    COL_SOURCE = 3
    COL_DESCRIPTION = 4
    COL_OBJECT = 5

    def __init__(self, parent, config, initial_query=''):
        super().__init__(
            title=_('Find podcast metadata online'),
            transient_for=parent,
            modal=True,
        )

        self.config = config
        self.selected_podcast = None

        self.add_buttons(
            _('_Cancel'), Gtk.ResponseType.CANCEL,
            _('_Use Selected'), Gtk.ResponseType.OK,
        )
        self.set_default_response(Gtk.ResponseType.OK)
        self.set_border_width(12)
        self.set_default_size(1050, 700)

        area = self.get_content_area()
        outer = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8)
        outer.set_hexpand(True)
        outer.set_vexpand(True)
        area.add(outer)

        search_row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        outer.pack_start(search_row, False, False, 0)

        self.search_entry = Gtk.Entry()
        self.search_entry.set_hexpand(True)
        self.search_entry.set_text(initial_query or '')
        self.search_entry.set_activates_default(False)
        search_row.pack_start(self.search_entry, True, True, 0)

        self.search_button = Gtk.Button.new_with_label(_('Search'))
        self.search_button.connect('clicked', self.on_search_podcasts_clicked)
        search_row.pack_start(self.search_button, False, False, 0)

        self.status_label = Gtk.Label(label='', xalign=0)
        outer.pack_start(self.status_label, False, False, 0)

        self.store = Gtk.ListStore(str, str, str, str, str, object)

        self.tree = Gtk.TreeView(model=self.store)
        self.tree.set_headers_visible(True)

        for title, column_id, width in (
            (_('Title'), self.COL_TITLE, 240),
            (_('Feed URL'), self.COL_FEED_URL, 300),
            (_('Website'), self.COL_WEBSITE_URL, 220),
            (_('Source'), self.COL_SOURCE, 140),
        ):
            renderer = Gtk.CellRendererText()
            renderer.set_property('ellipsize', 3)  # Pango.EllipsizeMode.END without new import
            column = Gtk.TreeViewColumn(title, renderer, text=column_id)
            column.set_resizable(True)
            column.set_min_width(width)
            self.tree.append_column(column)

        selection = self.tree.get_selection()
        selection.set_mode(Gtk.SelectionMode.SINGLE)
        selection.connect('changed', self.on_selection_changed)

        self.tree.connect('row-activated', self.on_row_activated)

        sw = Gtk.ScrolledWindow()
        sw.set_hexpand(True)
        sw.set_vexpand(True)
        sw.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        sw.add(self.tree)
        outer.pack_start(sw, True, True, 0)

        self.description = Gtk.TextView(wrap_mode=Gtk.WrapMode.WORD)
        self.description.set_editable(False)
        self.description.set_cursor_visible(False)

        desc_sw = Gtk.ScrolledWindow()
        desc_sw.set_hexpand(True)
        desc_sw.set_vexpand(False)
        desc_sw.set_min_content_height(120)
        desc_sw.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        desc_sw.add(self.description)
        outer.pack_start(desc_sw, False, True, 0)

        self.show_all()

        if initial_query:
            GLib.idle_add(self.on_search_podcasts_clicked, self.search_button)

    def on_search_podcasts_clicked(self, button):
        query = self.search_entry.get_text().strip()
        if not query:
            self.status_label.set_text(_('Enter a podcast name or keyword to search.'))
            return

        self.store.clear()
        self.selected_podcast = None
        self._set_description('')
        self.status_label.set_text(_('Searching...'))

        while Gtk.events_pending():
            Gtk.main_iteration_do(False)

        try:
            service = podcastmetadata.create_metadata_service(self.config, include_rss=False)

            podcasts = service.search_podcasts_from_all_providers(
                query,
                limit_per_provider=50,
                dedupe_across_sources=False,
            )

            source_counts = {}
            for podcast in podcasts:
                source = getattr(podcast, 'source', None) or '(unknown)'
                source_counts[source] = source_counts.get(source, 0) + 1

            logger.info(
                'Manual podcast metadata search results by source: %s',
                source_counts,
            )

        except Exception as exc:
            logger.warning('Podcast metadata search failed', exc_info=True)
            self.status_label.set_text(_('Search failed: %s') % str(exc))
            return

        for podcast in podcasts:
            self.store.append([
                podcast.title or '',
                podcast.feed_url or '',
                podcast.website_url or '',
                podcast.source or '',
                podcast.description or '',
                podcast,
            ])

        if podcasts:
            self.status_label.set_text(
                _('Found %(count)d result(s). Select one and click Use Selected.') %
                {'count': len(podcasts)}
            )
        else:
            self.status_label.set_text(_('No matching podcasts were found.'))

    def on_selection_changed(self, selection):
        model, tree_iter = selection.get_selected()
        if tree_iter is None:
            self.selected_podcast = None
            self._set_description('')
            return

        self.selected_podcast = model[tree_iter][self.COL_OBJECT]
        self._set_description(model[tree_iter][self.COL_DESCRIPTION] or '')

    def on_row_activated(self, tree, path, column):
        selection = tree.get_selection()
        self.on_selection_changed(selection)
        self.response(Gtk.ResponseType.OK)

    def _set_description(self, text):
        buf = self.description.get_buffer()
        buf.set_text(text or '')

    def get_selected_podcast(self):
        return self.selected_podcast

#===============================================================================
class ManualPodcastMetadataApplyDialog(Gtk.Dialog):
    """Choose the metadata fields to copy into the manual podcast add/edit dialog."""

    FIELD_TITLE = 'title'
    FIELD_FEED_URL = 'feed_url'
    FIELD_WEBSITE_URL = 'website_url'
    FIELD_COVER_URL = 'cover_url'
    FIELD_SECTION = 'section'
    FIELD_DESCRIPTION = 'description'

    def __init__(self, parent, metadata, current_values=None, is_edit=False):
        super().__init__(
            title=_('Apply podcast metadata'),
            transient_for=parent,
            modal=True,
        )

        self.metadata = metadata
        self.current_values = current_values or {}
        self.is_edit = is_edit
        self.checkboxes = {}

        self.add_buttons(
            _('_Cancel'), Gtk.ResponseType.CANCEL,
            _('_Apply Selected'), Gtk.ResponseType.OK,
        )

        self.set_default_response(Gtk.ResponseType.OK)
        self.set_border_width(12)
        self.set_default_size(1050, 700)

        area = self.get_content_area()

        outer = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8)
        outer.set_hexpand(True)
        outer.set_vexpand(True)
        area.add(outer)

        note = Gtk.Label(
            label=_('Select the metadata fields to copy into the podcast settings dialog.'),
            xalign=0,
        )
        outer.pack_start(note, False, False, 0)

        # Place the row grid inside a ScrolledWindow in case there are many fields or the description is long.
        grid = Gtk.Grid(column_spacing=DEFAULT_COL_SPACING, row_spacing=DEFAULT_ROW_SPACING,
                        margin=DEFAULT_MARGIN)  # Was: 14, 10, undefined
        grid.set_hexpand(True)
        grid.set_vexpand(True)
        grid.set_column_homogeneous(False)

        grid_sw = Gtk.ScrolledWindow()
        grid_sw.set_hexpand(True)
        grid_sw.set_vexpand(True)
        grid_sw.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        grid_sw.add(grid)
        outer.pack_start(grid_sw, True, True, 0)

        # Format the grid with 4 columns: checkbox, field name, current value, online value.
        # Use CSS style classes to visually differentiate current vs online values.
        grid.attach(self._make_header_label(_('Use')), 0, 0, 1, 1)
        grid.attach(self._make_header_label(_('Field')), 1, 0, 1, 1)
        grid.attach(self._make_header_label(_('Current value')), 2, 0, 1, 1)
        grid.attach(self._make_header_label(_('Online value')), 3, 0, 1, 1)

        section = ''
        if getattr(metadata, 'categories', None):
            section = metadata.categories[0] or ''

        rows = [
            (
                self.FIELD_TITLE,
                _('Title'),
                current_values.get('title', ''),
                metadata.title or '',
                True,
            ),
            (
                self.FIELD_FEED_URL,
                _('Feed URL'),
                current_values.get('feed_url', ''),
                metadata.feed_url or '',
                not is_edit,
            ),
            (
                self.FIELD_WEBSITE_URL,
                _('Website Link'),
                current_values.get('website_url', ''),
                metadata.website_url or '',
                True,
            ),
            (
                self.FIELD_COVER_URL,
                _('Cover Art URL'),
                current_values.get('cover_url', ''),
                metadata.image_url or '',
                True,
            ),
            (
                self.FIELD_SECTION,
                _('Section'),
                current_values.get('section', ''),
                section,
                False,
            ),
            (
                self.FIELD_DESCRIPTION,
                _('Description'),
                current_values.get('description', ''),
                metadata.description or '',
                True,
            ),
        ]

        row_num = 1

        # Loop to create a row for each metadata field with a checkbox, field label,
        # current value, and online value.
        for field_name, label, current_value, online_value, default_checked in rows:
            has_online_value = bool((online_value or '').strip())

            checkbox = Gtk.CheckButton()
            checkbox.set_active(default_checked and has_online_value)
            checkbox.set_sensitive(has_online_value)
            self.checkboxes[field_name] = checkbox

            # Format field within an EventBox to highlight them.
            field_label = Gtk.Label()
            field_label.set_markup('<b>%s</b>' % html.escape(label))
            field_label.set_xalign(0)

            # Put current and online values in an EventBox to get a visible background.
            # The description field gets a multi-line TextView inside a ScrolledWindow,
            # while other fields get a single-line Label. Both use CSS classes to
            # visually differentiate current vs online values.
            if field_name == self.FIELD_DESCRIPTION:
                current_box = self._make_description_box(
                    current_value,
                    'metadata-current-value',
                )
                online_box = self._make_description_box(
                    online_value,
                    'metadata-online-value',
                )
            else:
                current_box = self._make_value_box(
                    current_value,
                    'metadata-current-value',
                )
                online_box = self._make_value_box(
                    online_value,
                    'metadata-online-value',
                )

            grid.attach(checkbox, 0, row_num, 1, 1)
            grid.attach(field_label, 1, row_num, 1, 1)
            grid.attach(current_box, 2, row_num, 1, 1)
            grid.attach(online_box, 3, row_num, 1, 1)

            row_num += 1

        self.show_all()

    def _shorten(self, value, max_len=180):
        value = (value or '').strip().replace('\r', ' ').replace('\n', ' ')
        if len(value) > max_len:
            return value[:max_len - 3] + '...'
        return value

    def get_selected_fields(self):
        return {
            field_name
            for field_name, checkbox in self.checkboxes.items()
            if checkbox.get_active()
        }

    def _make_header_label(self, text):
        label = Gtk.Label(label=text, xalign=0)
        label.get_style_context().add_class('metadata-apply-header')
        return label

    def _make_value_box(self, text, css_class):
        label = Gtk.Label(label=self._shorten(text), xalign=0)
        label.set_line_wrap(True)
        label.set_selectable(True)
        label.set_tooltip_text(text or '')

        # EventBox lets GTK apply a visible background around the label.
        box = Gtk.EventBox()
        box.set_visible_window(True)
        box.set_hexpand(True)
        box.get_style_context().add_class(css_class)
        box.add(label)

        return box

    def _make_description_box(self, text, css_class):
        text = text or ''

        textview = Gtk.TextView()
        textview.set_wrap_mode(Gtk.WrapMode.WORD)
        textview.set_editable(False)
        textview.set_cursor_visible(False)
        textview.set_hexpand(True)
        textview.set_vexpand(True)

        buf = textview.get_buffer()
        buf.set_text(text)

        # Apply the same visual styling class to the TextView.
        textview.get_style_context().add_class(css_class)

        sw = Gtk.ScrolledWindow()
        sw.set_hexpand(True)
        sw.set_vexpand(True)
        sw.set_min_content_height(140)
        sw.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        sw.add(textview)

        # Also apply styling to the scrolled window so the box stands out.
        sw.get_style_context().add_class(css_class)

        return sw

#===============================================================================
class ManualPodcastDialog(Gtk.Dialog):

    def __init__(self, parent, config, podcast=None, section_names=None):
        self.config = config
        self.podcast = podcast
        self.is_edit = podcast is not None
        self.metadata_image_url = None

        super().__init__(
            title=_('Edit selected podcast') if self.is_edit else _('Add podcast manually'),
            transient_for=parent,
            modal=True,
        )

        self.add_buttons(
            _('_Cancel'), Gtk.ResponseType.CANCEL,
            _('_Save') if self.is_edit else _('_Add'), Gtk.ResponseType.OK,
        )
        self.set_default_response(Gtk.ResponseType.OK)
        self.set_border_width(12)
        self.set_default_size(760, 680)

        area = self.get_content_area()
        grid = Gtk.Grid(column_spacing=DEFAULT_COL_SPACING, row_spacing=DEFAULT_ROW_SPACING,
                        margin=DEFAULT_MARGIN)  # Was: 12, 8, 12
        area.add(grid)

        # Add a field for podcast title.
        self.podcast_title_entry = Gtk.Entry()
        self.podcast_title_entry.set_activates_default(True)

        self.find_metadata_button = Gtk.Button.new_with_label(_('Find online...'))
        self.find_metadata_button.set_tooltip_text(
            _('Search online podcast metadata providers and copy selected metadata into this form.')
        )
        self.find_metadata_button.connect('clicked', self.on_find_metadata_clicked)

        # Add a field for the feed URL - allows users to set a custom URL.
        self.podcast_feed_url_entry = Gtk.Entry()
        self.podcast_feed_url_entry.set_hexpand(True)

        # Add a field for the podcast's website link.
        self.podcast_website_link_entry = Gtk.Entry()
        self.podcast_website_link_entry.set_placeholder_text('https://example.com')

        # Add a field for the podcast cover/artwork URL.
        self.podcast_cover_url_entry = Gtk.Entry()
        self.podcast_cover_url_entry.set_placeholder_text('https://example.com/cover.jpg')
        self.podcast_cover_url_entry.set_hexpand(True)

        # Add a field for the podcast cover image.
        self.local_cover_file = None
        self.cover_preview_update_source_id = None

        self.podcast_cover_url_entry.connect('changed', self.on_cover_url_changed)

        self.cover_image = Gtk.Image()
        self.cover_image.set_pixel_size(160)

        self.cover_status_label = Gtk.Label(label='', xalign=0)
        self.cover_status_label.set_line_wrap(True)

        self.choose_cover_file_button = Gtk.Button.new_with_label(_('Choose JPG...'))
        self.choose_cover_file_button.set_tooltip_text(
            _('Choose a local JPG file to use as this podcast cover.')
        )
        self.choose_cover_file_button.connect('clicked', self.on_choose_cover_file_clicked)

        self.clear_cover_file_button = Gtk.Button.new_with_label(_('Clear local file'))
        self.clear_cover_file_button.set_tooltip_text(
            _('Clear the selected local cover file.')
        )
        self.clear_cover_file_button.connect('clicked', self.on_clear_cover_file_clicked)

        # Add fields for the podcast cover art.
        cover_button_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        cover_button_box.pack_start(self.choose_cover_file_button, False, False, 0)
        cover_button_box.pack_start(self.clear_cover_file_button, False, False, 0)

        cover_info_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6)
        cover_info_box.set_hexpand(True)
        cover_info_box.pack_start(self.cover_status_label, False, False, 0)
        cover_info_box.pack_start(cover_button_box, False, False, 0)

        cover_preview_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=12)
        cover_preview_box.set_hexpand(True)
        cover_preview_box.pack_start(self.cover_image, False, False, 0)
        cover_preview_box.pack_start(cover_info_box, True, True, 0)

        # Add a field for the podcast display section - use Other as the default.
        self.podcast_section_combo = Gtk.ComboBoxText.new_with_entry()
        self.podcast_section_combo.set_hexpand(True)

        for section in section_names or [_('Other')]:
            self.podcast_section_combo.append_text(section)

        self._set_section_text(_('Other'))

        # Add a scrollable window for the podcast description.
        self.podcast_description = Gtk.TextView(wrap_mode=Gtk.WrapMode.WORD)
        podcast_desc_sw = Gtk.ScrolledWindow()
        podcast_desc_sw.set_hexpand(True)
        podcast_desc_sw.set_vexpand(True)
        podcast_desc_sw.add(self.podcast_description)

        # Loop through the fields and add them to the grid with labels in the
        # first column and widgets in the second column.
        row = 0

        title_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        title_box.set_hexpand(True)
        title_box.pack_start(self.podcast_title_entry, True, True, 0)
        title_box.pack_start(self.find_metadata_button, False, False, 0)

        for label, widget in (
            (_('Title'), title_box),
            (_('Feed URL'), self.podcast_feed_url_entry),
            (_('Website Link'), self.podcast_website_link_entry),
            (_('Cover Art URL'), self.podcast_cover_url_entry),
            (_('Cover Preview'), cover_preview_box),
            (_('Section'), self.podcast_section_combo),
            (_('Description'), podcast_desc_sw),
        ):
            lbl = Gtk.Label(label=label, xalign=0)
            grid.attach(lbl, 0, row, 1, 1)
            grid.attach(widget, 1, row, 1, 1)
            row += 1

        # If editing an existing podcast, populate the fields with the current data
        # otherwise leave them blank for the user to fill in.
        if self.is_edit:
            self.podcast_title_entry.set_text(podcast.title or '')
            self.podcast_feed_url_entry.set_text(podcast.url or '')
            self.podcast_website_link_entry.set_text(podcast.link or '')
            self.podcast_cover_url_entry.set_text(getattr(podcast, 'cover_url', None) or '')
            self._set_section_text(getattr(podcast, 'section', '') or _('Other'))
            buf = self.podcast_description.get_buffer()
            buf.set_text((podcast.description or '').strip())
            self.metadata_image_url = getattr(podcast, 'cover_url', None)
            # Debug - display some of the podcast attributes to troubleshoot.
            #logger.warning('podcast title: %s', getattr(podcast, 'title', None))
            #logger.warning('podcast.url: %s', getattr(podcast, 'url', None))
            #logger.warning('podcast.link: %s', getattr(podcast, 'link', None))
            #logger.warning('podcast.cover_file: %s', getattr(podcast, 'cover_file', None))
            #logger.warning('podcast.cover_url: %s', getattr(podcast, 'cover_url', None))

        self.update_cover_preview()
        self.show_all()

    def on_find_metadata_clicked(self, button):
        query = self.podcast_title_entry.get_text().strip()

        dialog = ManualPodcastMetadataSearchDialog(
            self,
            self.config,
            initial_query=query,
        )

        try:
            response = dialog.run()
            if response != Gtk.ResponseType.OK:
                return

            metadata = dialog.get_selected_podcast()
            if metadata is None:
                return

            metadata = self.enrich_selected_podcast_metadata(metadata)

        finally:
            dialog.destroy()

        self.choose_and_apply_podcast_metadata(metadata)

    def apply_metadata(self, metadata, selected_fields):
        """Copy selected online metadata into the manual podcast form.

        This intentionally overwrites fields in the dialog only. The user still
        has to click Add/Save before anything is written to the database.
        """
        if ManualPodcastMetadataApplyDialog.FIELD_TITLE in selected_fields:
            if metadata.title:
                self.podcast_title_entry.set_text(metadata.title)

        if ManualPodcastMetadataApplyDialog.FIELD_FEED_URL in selected_fields:
            if metadata.feed_url:
                self.podcast_feed_url_entry.set_text(metadata.feed_url)

        if ManualPodcastMetadataApplyDialog.FIELD_WEBSITE_URL in selected_fields:
            if metadata.website_url:
                self.podcast_website_link_entry.set_text(metadata.website_url)

        if ManualPodcastMetadataApplyDialog.FIELD_COVER_URL in selected_fields:
            if metadata.image_url:
                self.podcast_cover_url_entry.set_text(metadata.image_url)
                self.local_cover_file = None
                self.update_cover_preview()

        if ManualPodcastMetadataApplyDialog.FIELD_SECTION in selected_fields:
            if getattr(metadata, 'categories', None):
                section = metadata.categories[0] or ''
                if section:
                    self._set_section_text.set_text(section)

        if ManualPodcastMetadataApplyDialog.FIELD_DESCRIPTION in selected_fields:
            if metadata.description:
                buf = self.podcast_description.get_buffer()
                buf.set_text(metadata.description)

    def choose_and_apply_podcast_metadata(self, metadata):
        current_values = self.get_current_metadata_values()

        dialog = ManualPodcastMetadataApplyDialog(
            self,
            metadata,
            current_values=current_values,
            is_edit=self.is_edit,
        )

        try:
            response = dialog.run()
            if response != Gtk.ResponseType.OK:
                return

            selected_fields = dialog.get_selected_fields()
            if not selected_fields:
                return

        finally:
            dialog.destroy()

        self.apply_metadata(metadata, selected_fields)

    def enrich_selected_podcast_metadata(self, metadata):
        """Try to replace search-result metadata with fuller feed/provider metadata."""

        feed_url = getattr(metadata, 'feed_url', None)
        if not feed_url:
            return metadata

        try:
            service = podcastmetadata.create_metadata_service(self.config, include_rss=True)

            fuller_metadata = service.lookup_by_feed_url(feed_url)
            if fuller_metadata is not None:
                logger.info(
                    'Enriched podcast metadata from feed URL: source=%s old_desc_len=%d new_desc_len=%d',
                    getattr(fuller_metadata, 'source', None),
                    len(getattr(metadata, 'description', '') or ''),
                    len(getattr(fuller_metadata, 'description', '') or ''),
                )
                return fuller_metadata

        except Exception:
            logger.warning('Could not enrich selected podcast metadata', exc_info=True)

        return metadata

    def get_current_metadata_values(self):
        buf = self.podcast_description.get_buffer()

        return {
            'title': self.podcast_title_entry.get_text().strip(),
            'feed_url': self.podcast_feed_url_entry.get_text().strip(),
            'website_url': self.podcast_website_link_entry.get_text().strip(),
            'cover_url': self.podcast_cover_url_entry.get_text().strip(),
            'section': self._get_section_text(),
            'description': buf.get_text(
                buf.get_start_iter(),
                buf.get_end_iter(),
                True,
            ).strip(),
        }

    #---------------------------------------------------------------------------
    # Cover Preview Handling
    #---------------------------------------------------------------------------
    def on_cover_url_changed(self, entry):
        """Refresh preview shortly after the user changes the cover URL."""

        # If a URL is present, URL takes priority over a selected local file.
        if entry.get_text().strip():
            self.local_cover_file = None

        self.update_cover_file_buttons()

        if self.cover_preview_update_source_id:
            GLib.source_remove(self.cover_preview_update_source_id)

        self.cover_preview_update_source_id = GLib.timeout_add(
            700,
            self._delayed_cover_preview_update,
        )

    def _delayed_cover_preview_update(self):
        self.cover_preview_update_source_id = None
        self.update_cover_preview()
        return False

    def update_cover_file_buttons(self):
        has_url = bool(self.podcast_cover_url_entry.get_text().strip())

        # Local upload is available only when no Cover Art URL is entered.
        self.choose_cover_file_button.set_sensitive(not has_url)
        self.clear_cover_file_button.set_sensitive(
            not has_url and bool(self.local_cover_file)
        )

    def update_cover_preview(self):
        cover_url = self.podcast_cover_url_entry.get_text().strip()

        self.update_cover_file_buttons()

        if cover_url:
            self._set_cover_preview_from_url(cover_url)
            return

        if self.local_cover_file:
            self._set_cover_preview_from_file(self.local_cover_file)
            return

        # Editing an existing podcast with no cover URL may still have folder.jpg.
        if self.is_edit and self.podcast is not None:
            local_folder_jpg = os.path.join(self.podcast.save_dir, 'folder.jpg')
            if os.path.exists(local_folder_jpg):
                self._set_cover_preview_from_file(local_folder_jpg)
                self.cover_status_label.set_text(_('Current local cover: folder.jpg'))
                return

        self.cover_image.clear()
        self.cover_status_label.set_text(
            _('No cover selected. Enter a Cover Art URL or choose a local JPG file.')
        )

    def _set_cover_preview_from_file(self, filename):
        try:
            pixbuf = GdkPixbuf.Pixbuf.new_from_file_at_scale(
                filename,
                160,
                160,
                True,
            )
            self.cover_image.set_from_pixbuf(pixbuf)
            self.cover_status_label.set_text(filename)
        except Exception:
            logger.warning('Could not load cover preview from file: %s', filename, exc_info=True)
            self.cover_image.clear()
            self.cover_status_label.set_text(_('Could not preview selected cover file.'))

    def _set_cover_preview_from_url(self, url):
        try:
            response = util.urlopen(url, timeout=10)
            if response.status_code != 200:
                raise ValueError('%s returned status code %d' % (url, response.status_code))

            loader = GdkPixbuf.PixbufLoader()
            loader.write(response.content)
            loader.close()

            pixbuf = loader.get_pixbuf()
            if pixbuf is None:
                raise ValueError('URL did not contain a supported image.')

            scaled = pixbuf.scale_simple(
                160,
                160,
                GdkPixbuf.InterpType.BILINEAR,
            )

            self.cover_image.set_from_pixbuf(scaled)
            self.cover_status_label.set_text(_('Preview loaded from Cover Art URL.'))

        except Exception:
            logger.warning('Could not load cover preview from URL: %s', url, exc_info=True)
            self.cover_image.clear()
            self.cover_status_label.set_text(_('Could not preview image from Cover Art URL.'))

    def on_choose_cover_file_clicked(self, button):
        dialog = Gtk.FileChooserNative.new(
            _('Choose podcast cover JPG'),
            self,
            Gtk.FileChooserAction.OPEN,
            _('_Open'),
            _('_Cancel'),
        )

        jpg_filter = Gtk.FileFilter()
        jpg_filter.set_name(_('JPEG images (*.jpg, *.jpeg)'))
        jpg_filter.add_pattern('*.jpg')
        jpg_filter.add_pattern('*.jpeg')
        jpg_filter.add_pattern('*.JPG')
        jpg_filter.add_pattern('*.JPEG')
        dialog.add_filter(jpg_filter)

        all_filter = Gtk.FileFilter()
        all_filter.set_name(_('All files'))
        all_filter.add_pattern('*')
        dialog.add_filter(all_filter)

        try:
            response = dialog.run()

            if response == Gtk.ResponseType.ACCEPT:
                filename = dialog.get_filename()

                if filename:
                    self.local_cover_file = filename
                    self.update_cover_preview()

        finally:
            dialog.destroy()

    def on_clear_cover_file_clicked(self, button):
        self.local_cover_file = None
        self.update_cover_preview()

    #---------------------------------------------------------------------------
    # General/Helper Functions
    #---------------------------------------------------------------------------
    def get_data(self):
        """ Return the current values from the dialog fields."""
        buf = self.podcast_description.get_buffer()
        return {
            'title': self.podcast_title_entry.get_text().strip(),
            'url': self.podcast_feed_url_entry.get_text().strip(),
            'link': self.podcast_website_link_entry.get_text().strip(),
            'cover_url': self.podcast_cover_url_entry.get_text().strip(),
            'cover_file': self.local_cover_file,
            'section': self._get_section_text() or _('Other'),
            'description': buf.get_text(
                buf.get_start_iter(),
                buf.get_end_iter(),
                True,
            ).strip(),
        }

    def _get_section_text(self):
        child = self.podcast_section_combo.get_child()
        if child is not None:
            return child.get_text().strip()

        return self.podcast_section_combo.get_active_text() or ''

    def _set_section_text(self, section):
        """Helper function to set the podcast section text."""
        section = (section or '').strip() or _('Other')

        child = self.podcast_section_combo.get_child()
        if child is not None:
            child.set_text(section)

#===============================================================================
class ManualEpisodeMetadataSearchDialog(Gtk.Dialog):
    """Search online metadata for episodes belonging to the selected podcast."""

    COL_TITLE = 0
    COL_PUBLISHED = 1
    COL_SOURCE = 2
    COL_DESCRIPTION = 3
    COL_OBJECT = 4

    def __init__(self, parent, config, podcast, initial_query=''):
        super().__init__(
            title=_('Find episode metadata online'),
            transient_for=parent,
            modal=True,
        )

        self.config = config
        self.podcast = podcast
        self.selected_episode = None

        self.add_buttons(
            _('_Cancel'), Gtk.ResponseType.CANCEL,
            _('_Use Selected'), Gtk.ResponseType.OK,
        )
        self.set_default_response(Gtk.ResponseType.OK)
        self.set_border_width(12)
        self.set_default_size(1050, 700)

        area = self.get_content_area()

        outer = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8)
        outer.set_hexpand(True)
        outer.set_vexpand(True)
        area.add(outer)

        podcast_title = getattr(podcast, 'title', '') or getattr(podcast, 'url', '')
        info = Gtk.Label(
            label=_('Search episodes for: %s') % podcast_title,
            xalign=0,
        )
        info.set_line_wrap(True)
        outer.pack_start(info, False, False, 0)

        search_row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        outer.pack_start(search_row, False, False, 0)

        self.search_entry = Gtk.Entry()
        self.search_entry.set_hexpand(True)
        self.search_entry.set_placeholder_text(_('Optional episode title keyword'))
        self.search_entry.set_text(initial_query or '')
        search_row.pack_start(self.search_entry, True, True, 0)

        self.search_button = Gtk.Button.new_with_label(_('Search'))
        self.search_button.connect('clicked', self.on_search_episodes_clicked)
        search_row.pack_start(self.search_button, False, False, 0)

        self.status_label = Gtk.Label(label='', xalign=0)
        outer.pack_start(self.status_label, False, False, 0)

        self.store = Gtk.ListStore(str, str, str, str, object)

        self.tree = Gtk.TreeView(model=self.store)
        self.tree.set_headers_visible(True)

        for title, column_id, width in (
            (_('Title'), self.COL_TITLE, 360),
            (_('Published'), self.COL_PUBLISHED, 140),
            (_('Source'), self.COL_SOURCE, 140),
        ):
            renderer = Gtk.CellRendererText()
            renderer.set_property('ellipsize', 3)
            column = Gtk.TreeViewColumn(title, renderer, text=column_id)
            column.set_resizable(True)
            column.set_min_width(width)
            self.tree.append_column(column)

        selection = self.tree.get_selection()
        selection.set_mode(Gtk.SelectionMode.SINGLE)
        selection.connect('changed', self.on_selection_changed)

        self.tree.connect('row-activated', self.on_row_activated)

        sw = Gtk.ScrolledWindow()
        sw.set_hexpand(True)
        sw.set_vexpand(True)
        sw.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        sw.add(self.tree)
        outer.pack_start(sw, True, True, 0)

        self.description = Gtk.TextView(wrap_mode=Gtk.WrapMode.WORD)
        self.description.set_editable(False)
        self.description.set_cursor_visible(False)

        desc_sw = Gtk.ScrolledWindow()
        desc_sw.set_hexpand(True)
        desc_sw.set_vexpand(False)
        desc_sw.set_min_content_height(120)
        desc_sw.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        desc_sw.add(self.description)
        outer.pack_start(desc_sw, False, True, 0)

        self.show_all()

        GLib.idle_add(self.on_search_episodes_clicked, self.search_button)

    def on_search_episodes_clicked(self, button):
        query = self.search_entry.get_text().strip().lower()

        self.store.clear()
        self.selected_episode = None
        self._set_description('')
        self.status_label.set_text(_('Searching...'))

        while Gtk.events_pending():
            Gtk.main_iteration_do(False)

        try:
            episodes = self._search_episode_metadata(query)
        except Exception as exc:
            logger.warning('Episode metadata search failed', exc_info=True)
            self.status_label.set_text(_('Search failed: %s') % str(exc))
            return

        for episode in episodes:
            self.store.append([
                episode.title or '',
                self._format_published(episode.published),
                episode.source or '',
                episode.description or '',
                episode,
            ])

        if episodes:
            self.status_label.set_text(
                _('Found %(count)d episode result(s). Select one and click Use Selected.') %
                {'count': len(episodes)}
            )
        else:
            self.status_label.set_text(_('No matching episodes were found.'))

    def _search_episode_metadata(self, query):
        logger.info(
            'Episode metadata search: podcast=%r feed_url=%r query=%r',
            getattr(self.podcast, 'title', None),
            getattr(self.podcast, 'url', None),
            query,
        )

        service = podcastmetadata.create_metadata_service(self.config, include_rss=False)
        feed_url = getattr(self.podcast, 'url', '') or ''
        metadata_podcast = None

        if feed_url and not feed_url.startswith('manual://'):
            metadata_podcast = service.lookup_by_feed_url(feed_url)
            logger.info(
                'Episode metadata podcast lookup result: title=%r source=%r source_id=%r',
                getattr(metadata_podcast, 'title', None),
                getattr(metadata_podcast, 'source', None),
                getattr(metadata_podcast, 'source_id', None),
            )
        else:
            logger.warning('Skipping episode metadata lookup - no URL feed or manual URL feed')

        # If lookup-by-feed-url failed, search by podcast title and use the first plausible result.
        if metadata_podcast is None:
            podcast_title = getattr(self.podcast, 'title', '') or ''
            podcast_matches = service.search_podcasts_from_all_providers(
                podcast_title,
                limit_per_provider=10,
                dedupe_across_sources=False,
            )
            if podcast_matches:
                metadata_podcast = podcast_matches[0]

        if metadata_podcast is None:
            return []

        episodes = service.get_episodes_from_all_providers(
            metadata_podcast,
            limit=100,
        )

        episodes = service.rss_description_fallback(
            metadata_podcast,
            episodes,
            limit=100,
        )

        if query:
            episodes = [
                episode for episode in episodes
                if query in ((episode.title or '').lower())
                or query in ((episode.description or '').lower())
            ]

        # Log the sources of the returned episode metadata to help troubleshoot
        # where metadata is coming from and how well the RSS fallback is working.
        source_counts = {}
        for episode in episodes:
            source = getattr(episode, 'source', None) or '(unknown)'
            source_counts[source] = source_counts.get(source, 0) + 1

        logger.info(
            'Episode metadata search returned %d episode(s) after RSS description fallback',
            len(episodes)
        )
        logger.info(
            'Combined episode metadata results by source: %s', source_counts
        )

        return episodes

    def _format_published(self, published):
        if not published:
            return ''

        try:
            if isinstance(published, int):
                return _dt.datetime.fromtimestamp(published).strftime('%Y-%m-%d')
            if isinstance(published, str):
                return published[:10]
        except Exception:
            pass

        return str(published)

    def on_selection_changed(self, selection):
        model, tree_iter = selection.get_selected()
        if tree_iter is None:
            self.selected_episode = None
            self._set_description('')
            return

        self.selected_episode = model[tree_iter][self.COL_OBJECT]
        self._set_description(model[tree_iter][self.COL_DESCRIPTION] or '')

    def on_row_activated(self, tree, path, column):
        selection = tree.get_selection()
        self.on_selection_changed(selection)
        self.response(Gtk.ResponseType.OK)

    def _set_description(self, text):
        buf = self.description.get_buffer()
        buf.set_text(text or '')

    def get_selected_episode(self):
        return self.selected_episode

#===============================================================================
class ManualEpisodeMetadataApplyDialog(Gtk.Dialog):
    """Choose the metadata fields to copy into the manual episode add/edit dialog."""

    FIELD_TITLE = 'title'
    FIELD_MEDIA_URL = 'media_url'
    FIELD_LINK = 'link'
    FIELD_DESCRIPTION = 'description'
    FIELD_PUBLISHED = 'published'
    FIELD_SEASON = 'season'
    FIELD_EPISODE = 'episode'
    FIELD_GUID = 'guid'
    FIELD_EPISODE_ART_URL = 'episode_art_url'
    FIELD_DURATION = 'duration'

    def __init__(self, parent, metadata, current_values=None, is_edit=False,
             value_column_title=None, note_text=None):
        super().__init__(
            title=_('Apply episode metadata'),
            transient_for=parent,
            modal=True,
        )

        self.metadata = metadata
        self.current_values = current_values or {}
        self.is_edit = is_edit
        self.checkboxes = {}

        self.add_buttons(
            _('_Cancel'), Gtk.ResponseType.CANCEL,
            _('_Apply Selected'), Gtk.ResponseType.OK,
        )

        self.set_default_response(Gtk.ResponseType.OK)
        self.set_border_width(12)
        self.set_default_size(1050, 700)

        area = self.get_content_area()

        outer = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=8)
        outer.set_hexpand(True)
        outer.set_vexpand(True)
        area.add(outer)

        note = Gtk.Label(
            label=note_text or _('Select the episode metadata fields to copy into the episode dialog.'),
            xalign=0,
        )
        outer.pack_start(note, False, False, 0)

        # Place the row grid inside a ScrolledWindow in case there are many fields or the description is long.
        grid = Gtk.Grid(column_spacing=DEFAULT_COL_SPACING, row_spacing=DEFAULT_ROW_SPACING,
                        margin=DEFAULT_MARGIN)  # Was: 14, 10, undefined
        grid.set_hexpand(True)
        grid.set_vexpand(True)
        grid.set_column_homogeneous(False)

        grid_sw = Gtk.ScrolledWindow()
        grid_sw.set_hexpand(True)
        grid_sw.set_vexpand(True)
        grid_sw.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        grid_sw.add(grid)
        outer.pack_start(grid_sw, True, True, 0)

        # Format the grid with 4 columns: checkbox, field name, current value, online value.
        # Use CSS style classes to visually differentiate current vs online values.
        grid.attach(self._make_header_label(_('Use')), 0, 0, 1, 1)
        grid.attach(self._make_header_label(_('Field')), 1, 0, 1, 1)
        grid.attach(self._make_header_label(_('Current value')), 2, 0, 1, 1)
        grid.attach(self._make_header_label(value_column_title or _('Online value')),3, 0, 1, 1)

        rows = [
            (self.FIELD_TITLE, _('Title'), current_values.get('title', ''), metadata.title or '', True),
            (self.FIELD_MEDIA_URL, _('Media URL'), current_values.get('media_url', ''), metadata.url or '', not is_edit),
            (self.FIELD_LINK, _('Episode page link'), current_values.get('link', ''), metadata.link or '', True),
            (self.FIELD_DESCRIPTION, _('Description'), current_values.get('description', ''), metadata.description or '', True),
            (self.FIELD_PUBLISHED, _('Published'), current_values.get('published', ''), self._format_published(metadata.published), True),
            (self.FIELD_SEASON, _('Season'), current_values.get('season', ''), self._value(metadata.season), True),
            (self.FIELD_EPISODE, _('Episode #'), current_values.get('episode', ''), self._value(metadata.number), True),
            (self.FIELD_GUID, _('GUID'), current_values.get('guid', ''), metadata.guid or '', False),
            (self.FIELD_EPISODE_ART_URL, _('Episode Art URL'), current_values.get('episode_art_url', ''), metadata.image_url or '', True),
            (self.FIELD_DURATION, _('Duration'), current_values.get('duration', ''), self._value(metadata.duration), True),
        ]

        row_num = 1

        # Loop to create a row for each metadata field with a checkbox, field label,
        # current value, and online value.
        for field_name, label, current_value, online_value, default_checked in rows:
            has_online_value = bool((online_value or '').strip())

            checkbox = Gtk.CheckButton()
            checkbox.set_active(default_checked and has_online_value)
            checkbox.set_sensitive(has_online_value)
            self.checkboxes[field_name] = checkbox

            # Format field within an EventBox to highlight them.
            field_label = Gtk.Label()
            field_label.set_markup('<b>%s</b>' % html.escape(label))
            field_label.set_xalign(0)

            # Put current and online values in an EventBox to get a visible background.
            # The description field gets a multi-line TextView inside a ScrolledWindow,
            # while other fields get a single-line Label. Both use CSS classes to
            # visually differentiate current vs online values.
            if field_name == self.FIELD_DESCRIPTION:
                current_box = self._make_description_box(
                    current_value,
                    'metadata-current-value',
                )
                online_box = self._make_description_box(
                    online_value,
                    'metadata-online-value',
                )
            else:
                current_box = self._make_value_box(
                    current_value,
                    'metadata-current-value',
                )
                online_box = self._make_value_box(
                    online_value,
                    'metadata-online-value',
                )

            grid.attach(checkbox, 0, row_num, 1, 1)
            grid.attach(field_label, 1, row_num, 1, 1)
            grid.attach(current_box, 2, row_num, 1, 1)
            grid.attach(online_box, 3, row_num, 1, 1)

            row_num += 1

        self.show_all()

    def _value(self, value):
        if value is None:
            return ''
        return str(value)

    def _format_published(self, published):
        if not published:
            return ''

        try:
            if isinstance(published, int):
                return _dt.datetime.fromtimestamp(published).strftime('%Y-%m-%d %H:%M')
            if isinstance(published, str):
                return published[:16].replace('T', ' ')
        except Exception:
            pass

        return str(published)

    def _shorten(self, value, max_len=180):
        value = (value or '').strip().replace('\r', ' ').replace('\n', ' ')
        if len(value) > max_len:
            return value[:max_len - 3] + '...'
        return value

    def get_selected_fields(self):
        return {
            field_name
            for field_name, checkbox in self.checkboxes.items()
            if checkbox.get_active()
        }

    def _make_header_label(self, text):
        label = Gtk.Label(label=text, xalign=0)
        label.get_style_context().add_class('metadata-apply-header')
        return label

    def _make_value_box(self, text, css_class):
        label = Gtk.Label(label=self._shorten(text), xalign=0)
        label.set_line_wrap(True)
        label.set_selectable(True)
        label.set_tooltip_text(text or '')

        # EventBox lets GTK apply a visible background around the label.
        box = Gtk.EventBox()
        box.set_visible_window(True)
        box.set_hexpand(True)
        box.get_style_context().add_class(css_class)
        box.add(label)

        return box

    def _make_description_box(self, text, css_class):
        text = text or ''

        textview = Gtk.TextView()
        textview.set_wrap_mode(Gtk.WrapMode.WORD)
        textview.set_editable(False)
        textview.set_cursor_visible(False)
        textview.set_hexpand(True)
        textview.set_vexpand(True)

        buf = textview.get_buffer()
        buf.set_text(text)

        # Apply the same visual styling class to the TextView.
        textview.get_style_context().add_class(css_class)

        sw = Gtk.ScrolledWindow()
        sw.set_hexpand(True)
        sw.set_vexpand(True)
        sw.set_min_content_height(140)
        sw.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        sw.add(textview)

        # Also apply styling to the scrolled window so the box stands out.
        sw.get_style_context().add_class(css_class)

        return sw

#===============================================================================
class ManualEpisodeDialog(Gtk.Dialog):

    def __init__(self, parent, config, podcasts, active_podcast=None, episode=None):
        self.config = config
        self.episode = episode
        self.is_edit = episode is not None

        super().__init__(
            title=_('Edit selected episode') if self.is_edit else _('Add episode manually'),
            transient_for=parent,
            modal=True,
        )
        self.add_buttons(
            _('_Cancel'), Gtk.ResponseType.CANCEL,
            _('_Save') if self.is_edit else _('_Add'), Gtk.ResponseType.OK,
        )
        self.set_default_response(Gtk.ResponseType.OK)
        self.set_border_width(12)
        self.set_resizable(True)
        self.set_default_size(760, 680)

        self._podcasts = list(podcasts)

        area = self.get_content_area()
        area.set_hexpand(True)
        area.set_vexpand(True)

        grid = Gtk.Grid(column_spacing=DEFAULT_COL_SPACING, row_spacing=DEFAULT_ROW_SPACING,
                        margin=DEFAULT_MARGIN)  # Was: 12, 8, 12
        grid.set_hexpand(True)
        grid.set_vexpand(True)
        area.add(grid)

        #-----------------------------------------------------------------------
        # NOTE: Fields are defined in the order they appear in the dialog from
        #       top to bottom.
        #-----------------------------------------------------------------------
        # Create a combo box to select which podcast the episode belongs to.
        # If editing an existing episode, pre-select the episode's current podcast.
        # If adding a new episode, pre-select the active podcast if provided,
        # otherwise default to the first podcast in the list.
        self.combo_podcast = Gtk.ComboBoxText()
        active_index = 0
        target_podcast = episode.channel if episode is not None else active_podcast
        for i, podcast in enumerate(self._podcasts):
            self.combo_podcast.append(str(i), podcast.title or podcast.url)
            if target_podcast is not None and podcast.url == target_podcast.url:
                active_index = i
        if self._podcasts:
            self.combo_podcast.set_active(active_index)

        # Create a label to display instructions for selecting a media file.
        # This is important because episode fields can be auto-populated
        # from the media file's metadata tags, so selecting a media file
        # is often the first step in adding/editing an episode.
        self.media_help_label = Gtk.Label(
            use_markup=True,
            label=_('<i>Select a media file first so the title, description, and published date fields can be populated.</i>'),
            xalign=0,
        )
        self.media_help_label.set_line_wrap(True)
        self.media_help_label.set_max_width_chars(100)

        # Create a file chooser button for selecting the episode media file.
        # If editing an existing episode, the media file field is initially blank
        # since the assumption is no change to the media file will be made unless
        # the user intentionally selects a new media file. This is to prevent
        # unintentional overwriting of existing metadata.
        # If adding a new episode, the media file field is also initially blank but
        # the "Replace media file from selected source" option is checked by default
        # since there is no existing media file or metadata to overwrite, so it's
        # more likely the user will want to copy metadata from the selected media file.
        # Once a media file has been selected, the "Current media file" field is
        # updated to show the selected file path. Once a file has been selected,
        # the "Read tags..." button can be used to copy metadata from the media file
        # into the dialog fields.
        # NOTE: Replacing the existing media file causes existing metadata fields
        # to be overwritten with the new file's metadata, therefore a warning is
        # displayed giving the option to skip copying metadata from the new file.
        # If not editing an existing episode, default to copying metadata from
        # the new file since there is no existing file/metadata to overwrite.
        self.file_media = Gtk.FileChooserButton.new(_('Select media file'), Gtk.FileChooserAction.OPEN)
        self.file_media.set_hexpand(True)
        self.file_media.connect('selection-changed', self.on_media_file_selected)

        # Create a button that opens the a dialog to choose which metadata fields
        # contained in the media file (i.e., MP3 tags) to copy from the selected
        # media file.
        self.read_media_tags_button = Gtk.Button.new_with_label(_('Read tags...'))
        self.read_media_tags_button.set_tooltip_text(
            _('Read metadata tags from the selected media file and choose which fields to apply.')
        )
        self.read_media_tags_button.connect('clicked', self.on_read_media_tags_clicked)

        # Create a horizontal box to hold the media file chooser and the "Read tags..."
        # button next to each other.
        media_file_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        media_file_box.set_hexpand(True)
        media_file_box.pack_start(self.file_media, True, True, 0)
        media_file_box.pack_start(self.read_media_tags_button, False, False, 0)

        # Create a checkbox to choose whether to replace the existing media file with the
        # newly selected media file.
        self.check_replace_media = Gtk.CheckButton.new_with_label(_('Replace media file from selected source'))
        self.check_replace_media.set_active(not self.is_edit)

        # Create a field for the episode title.
        self.entry_title = Gtk.Entry()
        self.entry_title.set_activates_default(True)

        # Create a button that opens the ManualEpisodeMetadataSearchDialog to find
        # and apply online metadata for episodes from the selected podcast.
        self.find_episode_metadata_button = Gtk.Button.new_with_label(_('Find online...'))
        self.find_episode_metadata_button.set_tooltip_text(
            _('Search online metadata providers for episodes from the selected podcast.')
        )
        self.find_episode_metadata_button.connect('clicked', self.on_find_episode_metadata_clicked)

        # Create a horizontal box to hold the episode title entry and the "Find online..."
        # button next to each other.
        title_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        title_box.set_hexpand(True)
        title_box.pack_start(self.entry_title, True, True, 0)
        title_box.pack_start(self.find_episode_metadata_button, False, False, 0)

        # Create checkboxes for episode options: "Mark episode as new" and
        # "Store description as HTML".
        self.check_mark_new = Gtk.CheckButton.new_with_label(_('Mark episode as new'))
        self.check_mark_new.set_active(True)

        self.check_description_html = Gtk.CheckButton.new_with_label(_('Store description as HTML'))
        self.check_description_html.set_tooltip_text(
            _('Save the description field as HTML instead of plain text.')
        )

        # Create a horizontal box for displaying the "Mark as new" and
        # "Store description as HTML" options next to each other.
        episode_options_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=16)
        episode_options_box.set_hexpand(True)
        episode_options_box.pack_start(self.check_mark_new, False, False, 0)
        episode_options_box.pack_start(self.check_description_html, False, False, 0)

        # Create a multi-line text view for the episode description.
        self.text_description = Gtk.TextView(wrap_mode=Gtk.WrapMode.WORD)
        self.text_description.set_hexpand(True)
        self.text_description.set_vexpand(True)

        desc_sw = Gtk.ScrolledWindow()
        desc_sw.set_hexpand(True)
        desc_sw.set_vexpand(True)
        desc_sw.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        desc_sw.set_min_content_height(250)
        desc_sw.add(self.text_description)

        # Create a field for date/time the episode was published.
        self.entry_published = Gtk.Entry()
        self.entry_published.set_text(_dt.datetime.now().strftime('%Y-%m-%d %H:%M'))

        # Create a field for episode duration in seconds.
        self.spin_duration = Gtk.SpinButton.new_with_range(0, 999999, 1)
        self.spin_duration.set_tooltip_text(_('Episode duration in seconds'))

        # Create a horizontal box for displaying Published Date/Time and Duration (seconds).
        published_duration_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=12)
        published_duration_box.set_hexpand(True)

        published_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        published_box.pack_start(Gtk.Label(label=_(''), xalign=0), False, False, 0)
        published_box.pack_start(self.entry_published, True, True, 0)

        duration_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        duration_box.pack_start(Gtk.Label(label=_('Duration (seconds)'), xalign=0), False, False, 0)
        duration_box.pack_start(self.spin_duration, False, False, 0)

        published_duration_box.pack_start(published_box, True, True, 0)
        published_duration_box.pack_start(duration_box, False, False, 0)

        # Create a field for the URL to the webpage describing the episode.
        self.entry_link = Gtk.Entry()
        self.entry_link.set_placeholder_text('https://example.com/episode-page')

        # Create a field for the URL to the episode media file. This is optional
        # but can be used to pre-populate the media URL field if the media file
        # is already hosted online.
        self.entry_media_url = Gtk.Entry()
        self.entry_media_url.set_placeholder_text(_('Online media/enclosure URL'))

        # Create a field for the URL to the episode artwork. This is optional
        # but can be used to pre-populate the episode art URL field if the
        # artwork is already hosted online.
        self.entry_episode_art_url = Gtk.Entry()
        self.entry_episode_art_url.set_placeholder_text(_('URL for episode artwork'))

        # Create a preview image field and status label for the episode artwork URL
        # and place them in a vertical box to visually group them together.
        self.embedded_cover_image = Gtk.Image()
        self.embedded_cover_image.set_pixel_size(96)
        self.embedded_cover_image.set_halign(Gtk.Align.CENTER)

        self.embedded_cover_status_label = Gtk.Label(label='')
        self.embedded_cover_status_label.set_xalign(0.5)
        self.embedded_cover_status_label.set_justify(Gtk.Justification.CENTER)
        self.embedded_cover_status_label.set_halign(Gtk.Align.CENTER)
        self.embedded_cover_status_label.set_line_wrap(True)

        embedded_cover_box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4)
        embedded_cover_box.set_halign(Gtk.Align.CENTER)
        embedded_cover_box.pack_start(self.embedded_cover_image, False, False, 0)
        embedded_cover_box.pack_start(self.embedded_cover_status_label, False, False, 0)

        # Create spin buttons for season number and episode number.
        self.spin_season_num = Gtk.SpinButton.new_with_range(0, 9999, 1)
        self.spin_episode_num = Gtk.SpinButton.new_with_range(0, 9999, 1)

        # Create a grid to hold the season number and episode number fields
        # next to each other and place that box next to the embedded cover preview box
        # to visually group them together. Grouping these fields saves vertical space
        # in the dialog box.
        season_episode_left_box = Gtk.Grid(column_spacing=6, row_spacing=6)
        season_episode_left_box.set_hexpand(False)

        season_label = Gtk.Label(label=_('Season'), xalign=1)
        season_label.set_halign(Gtk.Align.END)

        episode_label = Gtk.Label(label=_('Episode #'), xalign=1)
        episode_label.set_halign(Gtk.Align.END)

        self.spin_season_num.set_halign(Gtk.Align.END)
        self.spin_season_num.set_size_request(80, -1)
        self.spin_episode_num.set_halign(Gtk.Align.END)
        self.spin_episode_num.set_size_request(80, -1)

        season_episode_left_box.attach(season_label, 0, 0, 1, 1)
        season_episode_left_box.attach(self.spin_season_num, 1, 0, 1, 1)

        season_episode_left_box.attach(episode_label, 0, 1, 1, 1)
        season_episode_left_box.attach(self.spin_episode_num, 1, 1, 1, 1)

        season_episode_box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=16)
        season_episode_box.set_hexpand(True)

        season_episode_box.pack_start(season_episode_left_box, True, True, 0)
        season_episode_box.pack_start(embedded_cover_box, False, False, 0)

        # Create a field for the episode GUID. This is optional and can be left blank
        # to auto-generate a GUID.
        self.entry_guid = Gtk.Entry()
        self.entry_guid.set_placeholder_text(_('Leave blank to auto-generate'))

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
        grid.attach(media_file_box, 1, row, 1, 1)
        row += 1

        if self.is_edit:
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
            (_('Episode Title'), title_box),
            (_(''), episode_options_box),
            (_('Description'), desc_sw),
            (_('Published'), published_duration_box),
            (_('Episode Page Link'), self.entry_link),
            (_('Media URL'), self.entry_media_url),
            (_('Episode Art URL'), self.entry_episode_art_url),
            (_(''), season_episode_box),
            (_('GUID Override'), self.entry_guid),
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

        # Populate form fields if editing an existing episode.
        if episode is not None:
            self.entry_title.set_text(episode.title or '')
            if episode.published:
                self.entry_published.set_text(
                    _dt.datetime.fromtimestamp(int(episode.published)).strftime('%Y-%m-%d %H:%M')
                )
            self.entry_link.set_text(episode.link or '')
            self.entry_media_url.set_text(episode.url or '')
            self.entry_episode_art_url.set_text(getattr(episode, 'episode_art_url', None) or '')
            self.spin_duration.set_value(int(getattr(episode, 'total_time', 0) or 0))
            self.entry_guid.set_text(episode.guid or '')
            self.spin_season_num.set_value(int(getattr(episode, 'season_num', 0) or 0))
            self.spin_episode_num.set_value(int(getattr(episode, 'episode_num', 0) or 0))
            self.check_mark_new.set_active(bool(getattr(episode, 'is_new', False)))
            self.check_replace_media.set_active(False)
            self.check_description_html.set_active(_episode_edit_description_is_html(episode))
            buf = self.text_description.get_buffer()
            buf.set_text(_episode_edit_description(episode).strip())

        # Show the dialog after creating all the widgets and populating the fields.
        self.show_all()

        # Update the embedded cover preview based on the cover image embedded in
        # the media file.
        self.update_embedded_cover_preview()

    #---------------------------------------------------------------------------
    # Public Methods - Button Callbacks
    #---------------------------------------------------------------------------
    def on_find_episode_metadata_clicked(self, button):
        """Open the ManualEpisodeMetadataSearchDialog to search for online metadata
           for episodes from the selected podcast and choose which metadata to
           apply to the episode dialog fields."""
        podcast = self.get_selected_podcast()
        if podcast is None:
            return

        query = self.entry_title.get_text().strip()

        dialog = ManualEpisodeMetadataSearchDialog(
            self,
            self.config,
            podcast,
            initial_query=query,
        )

        try:
            response = dialog.run()
            if response != Gtk.ResponseType.OK:
                return

            metadata = dialog.get_selected_episode()
            if metadata is None:
                return

        finally:
            dialog.destroy()

        self.choose_and_apply_episode_metadata(metadata)

    def on_media_file_selected(self, chooser):
        """When a media file is selected, update the help label to prompt
           the user to read tags from the media file."""
        filename = chooser.get_filename()
        if not filename:
            self.update_embedded_cover_preview()
            return

        self.media_help_label.set_text(
            _('Media file selected. Click "Read tags..." to choose which tag values to apply.')
        )

        self.update_embedded_cover_preview()

    def on_read_media_tags_clicked(self, button):
        """Read metadata tags from the selected media file and choose which fields
           to copy into the episode dialog."""
        filename = self._get_media_file_for_tag_reading()
        logger.info('Reading media tags from: %s', filename)

        if not filename:
            self._show_error(
                _('No media file available'),
                _(
                    'Select an MP3/media file, or edit an episode that already has '
                    'a downloaded local media file.'
                )
            )
            return

        try:
            tag_data = _extract_media_metadata(filename)
        except Exception as exc:
            logger.warning('Could not read media tags from %s', filename, exc_info=True)
            self._show_error(
                _('Could not read media tags'),
                str(exc),
            )
            return

        metadata = _media_metadata_to_episode_metadata(tag_data)
        self.update_embedded_cover_preview()
        self.choose_and_apply_media_tag_metadata(metadata)

    #---------------------------------------------------------------------------
    # Public Methods
    #---------------------------------------------------------------------------
    def apply_episode_metadata(self, metadata, selected_fields):
        if ManualEpisodeMetadataApplyDialog.FIELD_TITLE in selected_fields:
            if metadata.title:
                self.entry_title.set_text(metadata.title)

        if ManualEpisodeMetadataApplyDialog.FIELD_MEDIA_URL in selected_fields:
            if metadata.url:
                self.entry_media_url.set_text(metadata.url)

        if ManualEpisodeMetadataApplyDialog.FIELD_LINK in selected_fields:
            if metadata.link:
                self.entry_link.set_text(metadata.link)

        if ManualEpisodeMetadataApplyDialog.FIELD_DESCRIPTION in selected_fields:
            if metadata.description:
                buf = self.text_description.get_buffer()
                buf.set_text(metadata.description)

                # Most online metadata descriptions are HTML-ish.
                self.check_description_html.set_active(True)

        if ManualEpisodeMetadataApplyDialog.FIELD_PUBLISHED in selected_fields:
            published_text = self._metadata_published_to_text(metadata.published)
            if published_text:
                self.entry_published.set_text(published_text)

        if ManualEpisodeMetadataApplyDialog.FIELD_SEASON in selected_fields:
            if metadata.season is not None:
                self.spin_season_num.set_value(int(metadata.season or 0))

        if ManualEpisodeMetadataApplyDialog.FIELD_EPISODE in selected_fields:
            if metadata.number is not None:
                self.spin_episode_num.set_value(int(metadata.number or 0))

        if ManualEpisodeMetadataApplyDialog.FIELD_GUID in selected_fields:
            if metadata.guid:
                self.entry_guid.set_text(metadata.guid)

        if ManualEpisodeMetadataApplyDialog.FIELD_EPISODE_ART_URL in selected_fields:
            if metadata.image_url:
                self.entry_episode_art_url.set_text(metadata.image_url)

        if ManualEpisodeMetadataApplyDialog.FIELD_DURATION in selected_fields:
            if metadata.duration:
                self.spin_duration.set_value(int(metadata.duration or 0))

    def choose_and_apply_episode_metadata(self, metadata):
        current_values = self.get_current_episode_metadata_values()

        dialog = ManualEpisodeMetadataApplyDialog(
            self,
            metadata,
            current_values=current_values,
            is_edit=self.is_edit,
        )

        try:
            response = dialog.run()
            if response != Gtk.ResponseType.OK:
                return

            selected_fields = dialog.get_selected_fields()
            if not selected_fields:
                return

        finally:
            dialog.destroy()

        self.apply_episode_metadata(metadata, selected_fields)

    def choose_and_apply_media_tag_metadata(self, metadata):
        current_values = self.get_current_episode_metadata_values()

        dialog = ManualEpisodeMetadataApplyDialog(
            self,
            metadata,
            current_values=current_values,
            is_edit=self.is_edit,
            value_column_title=_('Tag value'),
            note_text=_('Select the media-file tag fields to copy into the episode dialog.'),
        )

        try:
            response = dialog.run()
            if response != Gtk.ResponseType.OK:
                return

            selected_fields = dialog.get_selected_fields()
            if not selected_fields:
                return

        finally:
            dialog.destroy()

        self.apply_episode_metadata(metadata, selected_fields)

    def get_current_episode_metadata_values(self):
        buf = self.text_description.get_buffer()

        return {
            'title': self.entry_title.get_text().strip(),
            'media_url': self.entry_media_url.get_text().strip(),
            'link': self.entry_link.get_text().strip(),
            'published': self.entry_published.get_text().strip(),
            'season': str(int(self.spin_season_num.get_value())),
            'episode': str(int(self.spin_episode_num.get_value())),
            'guid': self.entry_guid.get_text().strip(),
            'episode_art_url': self.entry_episode_art_url.get_text().strip(),
            'duration': str(int(self.spin_duration.get_value())),
            'description': buf.get_text(
                buf.get_start_iter(),
                buf.get_end_iter(),
                True,
            ).strip(),
        }

    def get_data(self):
        buf = self.text_description.get_buffer()

        return {
            'podcast': self.get_selected_podcast(),
            'title': self.entry_title.get_text().strip(),
            'media_file': self.file_media.get_filename(),
            'media_url': self.entry_media_url.get_text().strip(),
            'replace_media': self.check_replace_media.get_active(),
            'published_text': self.entry_published.get_text().strip(),
            'link': self.entry_link.get_text().strip(),
            'guid': self.entry_guid.get_text().strip(),
            'season_num': int(self.spin_season_num.get_value()),
            'episode_num': int(self.spin_episode_num.get_value()),
            'is_new': self.check_mark_new.get_active(),
            'description': buf.get_text(
                buf.get_start_iter(),
                buf.get_end_iter(),
                True,
            ).strip(),
            'description_is_html': self.check_description_html.get_active(),
            'episode_art_url': self.entry_episode_art_url.get_text().strip(),
            'total_time': int(self.spin_duration.get_value()),
        }

    def get_selected_podcast(self):
        idx = self.combo_podcast.get_active()
        return None if idx < 0 else self._podcasts[idx]

    def update_embedded_cover_preview(self):
        filename = self._get_media_file_for_tag_reading()

        if not filename:
            self.embedded_cover_image.clear()
            self.embedded_cover_status_label.set_text(_('Episode Cover Art\n(No local media file.)'))
            return

        try:
            image_data = _extract_embedded_cover_art(filename)
            pixbuf = _embedded_cover_art_to_pixbuf(image_data, size=96)

            if pixbuf is None:
                self.embedded_cover_image.clear()
                self.embedded_cover_status_label.set_text(_('Episode Cover Art\n(No embedded cover art found.)'))
                return

            self.embedded_cover_image.set_from_pixbuf(pixbuf)

            basename = os.path.basename(filename)
            self.embedded_cover_status_label.set_text(
                _('Episode Cover Art: %s') % basename
            )

        except Exception:
            logger.warning('Could not preview embedded cover art from %s', filename, exc_info=True)
            self.embedded_cover_image.clear()
            self.embedded_cover_status_label.set_text(_('Episode Cover Art\n(Could not preview embedded cover art.)'))

    #---------------------------------------------------------------------------
    # Private Methods
    #---------------------------------------------------------------------------
    def _get_media_file_for_tag_reading(self):
        """Return the best media file to use for reading tags.

        Priority:
            1. Newly selected file in the file chooser
            2. Existing local file for the episode being edited
            3. None
        """

        # 1. Newly selected media file.
        filename = self.file_media.get_filename()
        if filename:
            return filename

        # 2. Existing episode media file.
        if self.episode is not None:
            try:
                existing_filename = self.episode.local_filename(create=False)
            except Exception:
                logger.warning(
                    'Could not get existing local filename for episode: %r',
                    getattr(self.episode, 'title', None),
                    exc_info=True,
                )
                existing_filename = None

            if existing_filename and os.path.exists(existing_filename):
                return existing_filename

        # 3. Nothing available.
        return None

    def _metadata_published_to_text(self, published):
        if not published:
            return ''

        try:
            if isinstance(published, int):
                return _dt.datetime.fromtimestamp(published).strftime('%Y-%m-%d %H:%M')

            if isinstance(published, str):
                text = published.strip()
                text = text.replace('T', ' ')
                text = text.replace('Z', '')
                return text[:16]
        except Exception:
            logger.warning('Could not convert metadata published value: %r', published, exc_info=True)

        return str(published)

    def _show_error(self, title, message):
        dialog = Gtk.MessageDialog(
            transient_for=self,  #RobL - Formerly self.ui.main_window
            modal=True,
            message_type=Gtk.MessageType.ERROR,
            buttons=Gtk.ButtonsType.CLOSE,
            text=title,
        )
        dialog.format_secondary_text(message)
        dialog.run()
        dialog.destroy()

#===============================================================================
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
        self.set_default_size(760, 680)

        self._podcasts = list(podcasts)

        area = self.get_content_area()
        grid = Gtk.Grid(column_spacing=DEFAULT_COL_SPACING, row_spacing=DEFAULT_ROW_SPACING,
                        margin=DEFAULT_MARGIN)  # Was: 12, 8, 12
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

        # Create the "live batch status widgets that can be updated during the media file copy process.
        self.progress = Gtk.ProgressBar()
        self.progress.set_show_text(True)
        self.progress.set_text(_('Ready'))

        self.current_file_status = Gtk.Label(label=_('Current file: (none)'), xalign=0)

        self.status_log_buffer = Gtk.TextBuffer()
        self.status_log_view = Gtk.TextView.new_with_buffer(self.status_log_buffer)
        self.status_log_view.set_editable(False)
        self.status_log_view.set_cursor_visible(False)
        self.status_log_view.set_wrap_mode(Gtk.WrapMode.WORD_CHAR)

        self.status_log_scroll = Gtk.ScrolledWindow()
        self.status_log_scroll.set_min_content_height(120)
        self.status_log_scroll.set_hexpand(True)
        self.status_log_scroll.set_vexpand(True)
        self.status_log_scroll.add(self.status_log_view)

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

        # Add the live batch status widgets at the end so they show up below the form fields and can be updated during the import process.
        row += 1
        grid.attach(Gtk.Label(label=_('Progress'), xalign=0), 0, row, 1, 1)
        grid.attach(self.progress, 1, row, 1, 1)

        row += 1
        grid.attach(Gtk.Label(label=_('Now adding'), xalign=0), 0, row, 1, 1)
        grid.attach(self.current_file_status, 1, row, 1, 1)

        row += 1
        grid.attach(Gtk.Label(label=_('Status log'), xalign=0), 0, row, 1, 1)
        grid.attach(self.status_log_scroll, 1, row, 1, 1)

        # Show the dialog after creating all the widgets and populating the fields.
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

    def append_status_log(self, line):
        end_iter = self.status_log_buffer.get_end_iter()
        self.status_log_buffer.insert(end_iter, line + '\n')
        mark = self.status_log_buffer.create_mark(None, self.status_log_buffer.get_end_iter(), False)
        self.status_log_view.scroll_to_mark(mark, 0.0, True, 0.0, 1.0)

    def set_busy(self, busy):
        area = self.get_content_area()
        area.set_sensitive(not busy)
        self.get_widget_for_response(Gtk.ResponseType.OK).set_sensitive(not busy)
        self.get_widget_for_response(Gtk.ResponseType.CANCEL).set_sensitive(not busy)

    def run_batch_with_progress(self, controller, podcast, media_files, is_new=True, use_file_tags=True):
        total = len(media_files)
        if total <= 0:
            return []

        self.progress.set_fraction(0.0)
        self.progress.set_text(_('0/{total}').format(total=total))
        self.current_file_status.set_text(_('Current file: (starting)'))
        self.status_log_buffer.set_text('')
        self.append_status_log(_('Starting batch import of {total} file(s)...').format(total=total))
        self.set_busy(True)

        result = {'created': [], 'errors': []}
        done = threading.Event()

        def on_progress(index, total_count, source, created_episode, error):
            basename = os.path.basename(str(source))
            frac = float(index) / float(total_count) if total_count else 0.0
            self.progress.set_fraction(frac)
            self.progress.set_text(_('{index}/{total}').format(index=index, total=total_count))
            self.current_file_status.set_text(_('Current file: {name}').format(name=basename))
            if error is None:
                self.append_status_log(_('✅ Added: {name}').format(name=basename))
            else:
                self.append_status_log(_('❌ Failed: {name} — {err}').format(name=basename, err=str(error)))
            return False

        def worker():
            created, errors = controller.add_manual_episode_batch(
                podcast=podcast,
                media_files=media_files,
                is_new=is_new,
                use_file_tags=use_file_tags,
                on_progress=lambda *args: GLib.idle_add(on_progress, *args),
            )
            result['created'] = created
            result['errors'] = errors
            GLib.idle_add(done.set)

        threading.Thread(target=worker, daemon=True).start()

        while not done.is_set():
            Gtk.main_iteration_do(True)

        self.set_busy(False)
        self.append_status_log(_('Finished: {ok} added, {bad} failed').format(
            ok=len(result['created']), bad=len(result['errors'])
        ))
        return result['created']

#===============================================================================
class ManualEntryController(object):
    """ Controller for handling manual entry of podcasts and episodes,
        including opening dialogs and processing the data."""

    def __init__(self, ui):
        self.ui = ui

    #---------------------------------------------------------------------------
    # Public Methods - Action Installation
    #---------------------------------------------------------------------------
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

    #---------------------------------------------------------------------------
    # Public Methods - Action Callbacks
    #---------------------------------------------------------------------------
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

    #---------------------------------------------------------------------------
    # Public Methods - Dialog Openers
    #---------------------------------------------------------------------------
    def open_manual_add_podcast_dialog(self):
        """Open the dialog to manually create a new podcast."""

        dialog = ManualPodcastDialog(
            self.ui.main_window,
            self.ui.config,
            section_names=self._get_existing_podcast_sections(),
        )
        try:
            # Loop to allow the user to fix validation issues in the dialog without having
            # to re-enter all the data again. The dialog will only close when the user clicks
            # Cancel or successfully adds a podcast with valid data.
            while True:
                response = dialog.run()

                # User clicked Cancel, closed the dialog, or pressed Esc.
                if response != Gtk.ResponseType.OK:
                    return

                # Add the podcast with the new data from the dialog. If creation
                # fails (e.g. due to missing required fields), prompt the user to fix
                # the issues and retry.
                new_podcast = self.create_manual_podcast(**dialog.get_data())
                if new_podcast is not None:

                    # If the podcast was successfully created, refresh the UI to show the changes
                    # selecting the new podcast in the podcast list then exit the loop.
                    self._refresh_ui_after_podcast_change(
                        new_podcast,
                        select=True,
                        sections_changed=True,
                    )
                    break

        except Exception as exc:
            self._show_error(_('Add Podcast Manually -> New podcast not added'),
                             _('Could not add selected podcast due to following error:\n' + str(exc)))
        finally:
            dialog.destroy()

    def open_manual_edit_podcast_dialog(self):
        """Open the dialog to manually edit an existing podcast."""

        podcast = self._get_selected_existing_podcast()
        if podcast is None:
            return

        dialog = ManualPodcastDialog(
            self.ui.main_window,
            self.ui.config,
            podcast=podcast,
            section_names=self._get_existing_podcast_sections(),
        )
        try:
            # Loop to allow the user to fix validation issues in the dialog without having
            # to re-enter all the data again. The dialog will only close when the user clicks
            # Cancel or successfully adds a podcast with valid data.
            while True:
                response = dialog.run()

                # User clicked Cancel, closed the dialog, or pressed Esc.
                if response != Gtk.ResponseType.OK:
                    return

                # Update the podcast with the new data from the dialog. If the update
                # fails (e.g. due to missing required fields), do not proceed with
                # refreshing the UI and just return so the user can fix the issues
                # in the dialog. Also determine if the podcast section was changed
                # so we can refresh the UI appropriately after a successful update.
                old_section = (getattr(podcast, 'section', '') or '').strip()
                updated_podcast = self.update_manual_podcast(podcast, **dialog.get_data())
                if updated_podcast is not None:
                    new_section = (getattr(updated_podcast, 'section', '') or '').strip()
                    sections_changed = (new_section != old_section)

                    self._refresh_ui_after_podcast_change(
                        updated_podcast,
                        select=True,
                        sections_changed=sections_changed,
                    )
                    break

        except Exception as exc:
            self._show_error(_('Edit Podcast Manually -> Selected podcast not updated'),
                             _('Could not update podcast due to following error:\n' + str(exc)))
        finally:
            dialog.destroy()

    def open_manual_add_episode_dialog(self):
        """Open the dialog to manually add a new podcast episode."""

        podcasts = list(self.ui.model.get_podcasts())
        if not podcasts:
            self._show_error(
                _('No podcasts available'),
                _('Create a podcast manually or subscribe to one first.'),
            )
            return

        active = getattr(self.ui, 'active_channel', None)

        dialog = ManualEpisodeDialog(
            self.ui.main_window,
            self.ui.config,
            podcasts,
            active_podcast=active,
        )

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
        """Open the dialog to manually add a batch of new podcast episodes."""

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
                #episodes = self.add_manual_episode_batch(**dialog.get_data())
                #RobL--v--Update the controller to call the new dialog runner so it can call back
                #         to update the progress widgets during the batch import process.
                data = dialog.get_data()
                episodes = dialog.run_batch_with_progress(
                    controller=self,
                    podcast=data['podcast'],
                    media_files=data['media_files'],
                    is_new=data['is_new'],
                    use_file_tags=data['use_file_tags'],
                )
                #RobL--^
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

        dialog = ManualEpisodeDialog(
            self.ui.main_window,
            self.ui.config,
            podcasts,
            episode=episode,
        )

        try:
            response = dialog.run()
            if response == Gtk.ResponseType.OK:
                episode = self.update_manual_episode(episode, **dialog.get_data())
                self._refresh_ui_after_episode_change(episode)
        except Exception as exc:
            self._show_error(_('Could not update episode'), str(exc))
        finally:
            dialog.destroy()

    #---------------------------------------------------------------------------
    # Public Methods - Manual Podcast Creation/Update
    #---------------------------------------------------------------------------
    def create_manual_podcast(self, title, url, description='', link='', cover_url='',
                              cover_file='',  section=''):
        """Create a new podcast with the provided data from the add dialog."""

        # Verify a title was specified.
        title = (title or '').strip()
        if not title:
            self._show_error(_('Add Podcast Manually -> Title missing'),
                             _('A podcast title is required to save the podcast settings.'))
            return None  # Do not create the podcast if the title is missing.

        # Create a new podcast based on the PodcastClass.
        podcast = self.ui.model.PodcastClass(self.ui.model)

        # Verify the specified feed URL is valid.
        url = (url or '').strip()
        if not url:
            # If no URL was specified, create a unique manual feed URL based on the podcast title.
            podcast.url = self._build_unique_manual_podcast_url(title)
            #logger.warning("Add Podcast Manually -> Podcast feed URL not specified - creating manual url: %s", podcast.url)
        else:
            podcast.url = url

        # Verify the URL is reachable before saving it to avoid setting an invalid feed URL.
        # Note: manual podcasts using a manual:// feed URL are considered reachable.
        if not _is_url_reachable(podcast.url):
            if _ask_yes_no(self.ui.main_window,
                           _('Add Podcast Manually -> Confirm saving unreachable feed URL'),
                           _('Warning! The podcast feed URL provided is not reachable.\n\n' +
                             'Do you want to save this feed URL for the new podcast anyway?')
                          ) != Gtk.ResponseType.YES:
                #logger.warning("Add Podcast Manually -> Unreachable feed URL was NOT saved: %s", podcast.url)
                return None  # Do not add the podcast with an unreachable feed URL
            #else:
                #logger.warning("Add Podcast Manually -> Unreachable feed URL saved: %s", podcast.url)

        podcast.title = title
        podcast.link = link.strip()
        podcast.description = description.strip()
        podcast.cover_url = (cover_url or '').strip() or None
        podcast.payment_url = None
        podcast.section = (section or '').strip() or _('Other')
        podcast.download_folder = None
        podcast.save()
        podcast.get_save_dir(force_new=True)
        podcast.save()
        self.ui.db.commit() # Added to commit changes to database

        # Store the cover art for the podcast if a cover URL or file was provided.
        self._store_manual_podcast_cover(
            podcast,
            cover_url=cover_url,
            cover_file=cover_file,
        )
        return podcast

    def update_manual_podcast(self, podcast, title, url, link='', cover_url='',
                              cover_file='', section='', description=''):
        """Update the selected podcast with the provided data from the edit dialog."""

        title = (title or '').strip()
        if not title:
            self._show_error(_('Edit Podcast Manually -> Title missing'),
                             _('A podcast title is required to save the podcast settings.'))
            return None  # Do not update the podcast if the title is missing.

        old_title = podcast.title or ''
        if title != old_title:
            podcast.rename(title)
        else:
            podcast.title = title

        url = (url or '').strip()
        if not url:
            self._show_error(_('Edit Podcast Manually -> Feed URL missing'),
                             _('A podcast feed URL is required to save the podcast settings.\n' +
                               'Note - for podcasts with no feed, use:\n' +
                               '       manual://podcast/podcast-title (replacing all whitespace with dashes)'))
            return None  # Do not update the podcast if the feed URL is missing.

        old_url = podcast.url
        new_url = url

        # Verify the new URL is unique among the other podcasts in the model.
        for channel in getattr(self.ui, 'channels', []):
            if channel is not podcast and getattr(channel, 'url', None) == new_url:
                if _ask_yes_no(self.ui.main_window,
                               _('Edit Podcast Manually -> Confirm saving duplicate feed URL'),
                               _('Warning! Another podcast already uses this feed URL.\n\n' +
                                 'Do you want to save this feed URL for the selected podcast anyway?')
                              ) != Gtk.ResponseType.YES:
                    #logger.warning("Edit Podcast Manually -> Duplicate feed URL was NOT saved: %s", new_url)
                    return None  # Do not update the podcast with the duplicate feed URL
                #else:
                    #logger.warning("Edit Podcast Manually -> Duplicate feed URL saved: %s", new_url)

        # If the feed URL changed, verify the URL is reachable before saving it to avoid
        # setting an invalid feed URL that cannot be used to update the podcast later.
        # If the URL is reachable, clear the cover art cache for both the old and new URL
        # to ensure the cover art gets properly updated. If not reachable, warn the user
        # but still allow them to save the new URL in case they want to fix it later.
        if new_url != old_url:
            if _is_url_reachable(new_url):
                podcast.url = new_url
            else:
                if _ask_yes_no(self.ui.main_window,
                               _('Edit Podcast Manually -> Confirm saving unreachable feed URL'),
                               _('Warning! The podcast feed URL provided is not reachable.\n\n' +
                                 'Do you want to save this feed URL for the selected podcast anyway?')
                              ) != Gtk.ResponseType.YES:
                    #logger.warning("Edit Podcast Manually -> Unreachable feed URL was NOT saved: %s", new_url)
                    return None  # Do not update the podcast with an unreachable feed URL
                else:
                    #logger.warning("Edit Podcast Manually -> Unreachable feed URL saved: %s", new_url)
                    podcast.url = new_url

            #logger.warning("Edit Podcast Manually -> Podcast feed URL changed - OLD: %s, NEW: %s", old_url, new_url)
        #else:
            #logger.warning("Edit Podcast Manually -> Podcast feed URL did NOT change: %s", old_url)

        podcast.link = link.strip()
        podcast.description = description.strip()
        podcast.section = (section or '').strip() or _('Other')

        old_cover_url = getattr(podcast, 'cover_url', None)
        new_cover_url = (cover_url or '').strip() or None
        if new_cover_url != old_cover_url:
            podcast.cover_url = new_cover_url

        podcast.save()
        self.ui.db.commit()  # Added to commit changes to database.

        # If the cover URL changed or a local cover file was selected, store the new cover art for the podcast.
        #   Cover URL changed  → download URL and save folder.jpg
        #   Local JPG selected → copy local JPG and save folder.jpg
        #   No cover changes   → leave folder.jpg alone
        cover_url_changed = new_cover_url != old_cover_url
        local_cover_selected = bool((cover_file or '').strip())

        if cover_url_changed or local_cover_selected:
            self._store_manual_podcast_cover(
                podcast,
                cover_url=new_cover_url or '',
                cover_file=cover_file or '',
            )

        # Clear the cover art cache for both the old and new URL to ensure the cover art gets
        # properly updated in the UI. This is done whether the URL is updated or not since the
        # cache gets refreshed the next time the podcast is displayed.
        self.ui.podcast_list_model.clear_cover_cache(old_url)
        self.ui.podcast_list_model.clear_cover_cache(new_url)

        return podcast

    #---------------------------------------------------------------------------
    # Public Methods - Manual Episode Creation/Update
    #---------------------------------------------------------------------------
    def add_manual_episode(self, podcast, title, media_file, published_text,
                           link='', guid='', season_num=0, episode_num=0,
                           is_new=True, description='', description_is_html=False,
                           replace_media=True, media_url='', episode_art_url='',
                           total_time=0):
        if podcast is None:
            raise ManualEntryError(_('A podcast must be selected.'))

        media_url = (media_url or '').strip()
        if not media_file and not media_url:
            raise ManualEntryError(_('A media file or online media URL is required.'))

        source = None
        metadata = {
            'title': '',
            'description': '',
            'published': int(time.time()),
        }

        if media_file:
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
            media_url=media_url,
            episode_art_url=episode_art_url,
            total_time=total_time,
            replace_media=bool(source),
            is_new_record=True,
        )

        episode.save()
        self._ensure_episode_in_channel_list(episode)
        if hasattr(podcast, '_determine_common_prefix'):
            podcast._determine_common_prefix()
        podcast.save()
        self.ui.db.commit()  #RobL

        return episode

    def add_manual_episode_batch(self, podcast, media_files, is_new=True, use_file_tags=True, on_progress=None):
        if podcast is None:
            raise ManualEntryError(_('A podcast must be selected.'))
        if not media_files:
            raise ManualEntryError(_('Select one or more media files.'))

        created = []
        errors = []
        total = len(media_files)

        # Iterate through the media files to add, and add them as episodes.
        for idx, media_file in enumerate(media_files, start=1):

            source = pathlib.Path(media_file).expanduser().resolve()
            if not source.exists() or not source.is_file():
                err = ManualEntryError(_('Selected media file was not found: {}').format(source))
                errors.append((str(source), err))
                if on_progress:
                    on_progress(idx, total, source, None, err)
                continue

            try:
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

                if on_progress:
                    on_progress(idx, total, source, episode, None)

            except Exception as exc:
                errors.append((str(source), exc))
                if on_progress:
                    on_progress(idx, total, source, None, exc)
                continue

        # Update the podcast after all episodes have been added.
        if hasattr(podcast, '_determine_common_prefix'):
            podcast._determine_common_prefix()
        podcast.save()
        self.ui.db.commit()  #RobL

        return created, errors

    def update_manual_episode(self, episode, podcast, title, media_file, replace_media,
                              published_text, link='', guid='', season_num=0, episode_num=0,
                              is_new=True, description='', description_is_html=False,
                              media_url='', episode_art_url='', total_time=0):
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
            media_url=media_url,
            episode_art_url=episode_art_url,
            total_time=total_time,
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
        self.ui.db.commit()  #RobL

        return episode

    #---------------------------------------------------------------------------
    # Private Methods - Helper Functions for Podcast/Episode Creation/Update
    #---------------------------------------------------------------------------
    def _apply_episode_fields(self, episode, podcast, title, published, link, guid,
                              season_num, episode_num, is_new, description,
                              description_is_html=False,
                              media_source=None, media_url='', episode_art_url='',
                              total_time=0, replace_media=False,
                              is_new_record=False):
        old_destination = None
        if getattr(episode, 'download_filename', None):
            old_destination = episode.local_filename(create=False, check_only=True)

        episode.title = title

        episode_art_url = (episode_art_url or '').strip()
        if hasattr(episode, 'episode_art_url'):
            episode.episode_art_url = episode_art_url or None

        if total_time:
            episode.total_time = int(total_time or 0)

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
        episode.published = published
        episode.payment_url = None
        episode.current_position = 0
        episode.current_position_updated = 0
        episode.last_playback = 0 if is_new else int(time.time())

        media_url = (media_url or '').strip()
        episode.link = link.strip() or (
            media_source.as_uri() if media_source is not None else episode.link
        )

        if not total_time:
            episode.total_time = getattr(episode, 'total_time', 0) or 0

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
            if media_url:
                episode.url = media_url
                episode.mime_type = mimetypes.guess_type(media_url)[0] or episode.mime_type or 'application/octet-stream'
                episode.file_size = getattr(episode, 'file_size', 0) or 0

                # Do not mark as downloaded if this is an online-only episode.
                if is_new_record:
                    episode.state = gpodder.STATE_NORMAL

            elif replace_media:
                raise ManualEntryError(_('A replacement media file or online media URL is required.'))

            else:
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

    def _ensure_episode_in_channel_list(self, episode):
        podcast = episode.channel
        if episode not in podcast.children:
            podcast.children.append(episode)
        podcast.children[:] = list(Model.sort_episodes_by_pubdate(podcast.children, reverse=True))

    def _get_existing_podcast_sections(self):
        """Get the list of existing podcast section names."""
        sections = set()

        for podcast in self.ui.model.get_podcasts():
            section = (getattr(podcast, 'section', '') or '').strip()
            if section:
                sections.add(section)

        if not sections:
            sections.add(_('Other'))

        return sorted(sections, key=lambda value: value.lower())

    def _get_selected_existing_podcast(self):
        podcast = getattr(self.ui, 'active_channel', None)

        if podcast is None:
            self._show_error(
                _('No podcast selected'),
                _('Select a podcast first.')
            )
            return None

        if getattr(podcast, 'ALL_EPISODES_PROXY', False):
            self._show_error(
                _('All Episodes list selected'),
                _('Select a valid, existing podcast first.')
            )
            return None

        if not getattr(podcast, 'url', None):
            self._show_error(
                _('Invalid podcast selected'),
                _('Select a valid, existing podcast first.')
            )
            return None

        return podcast

    def _get_single_selected_episode(self):
        getter = getattr(self.ui, 'get_selected_episodes', None)
        if getter is None:
            return None
        episodes = list(getter())
        if len(episodes) != 1:
            return None
        return episodes[0]

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

    #---------------------------------------------------------------------------
    # Private Methods - Helper Functions for UI Refresh
    #---------------------------------------------------------------------------
    def _refresh_ui_after_podcast_change(self, podcast, select=False, sections_changed=False):
        select_url = podcast.url if select else None
        self.ui.update_podcast_list_model(
            select_url=select_url,
            sections_changed=sections_changed,
        )
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

    #---------------------------------------------------------------------------
    # Private Methods - Helper Functions for Podcast Cover Art Updates
    #---------------------------------------------------------------------------
    def _backup_existing_folder_jpg(self, destination):
        if not os.path.exists(destination):
            return

        dirname = os.path.dirname(destination)
        backup = os.path.join(dirname, 'old_cover.jpg')

        if os.path.exists(backup):
            timestamp = time.strftime('%Y%m%d-%H%M%S')
            backup = os.path.join(dirname, 'old_cover_%s.jpg' % timestamp)

        try:
            logger.info('Backing up existing cover: %s -> %s', destination, backup)
            os.replace(destination, backup)
        except Exception:
            logger.warning('Could not back up existing folder.jpg', exc_info=True)

    def _copy_local_cover_to_folder_jpg(self, source, destination):
        if not source or not os.path.exists(source):
            raise ManualEntryError(_('Selected cover image was not found.'))

        if not self._is_jpeg_file(source):
            raise ManualEntryError(_('Selected cover image must be a JPG file.'))

        logger.info('Copying local podcast cover: %s -> %s', source, destination)
        shutil.copyfile(source, destination)

    def _download_cover_url_to_folder_jpg(self, cover_url, destination):
        logger.info('Downloading manual podcast cover: %s', cover_url)

        response = util.urlopen(cover_url, timeout=15)
        if response.status_code != 200:
            raise ManualEntryError(
                _('Cover Art URL returned status code %d.') % response.status_code
            )

        loader = GdkPixbuf.PixbufLoader()
        loader.write(response.content)
        loader.close()

        pixbuf = loader.get_pixbuf()
        if pixbuf is None:
            raise ManualEntryError(_('Cover Art URL did not contain a supported image.'))

        # Always save as folder.jpg, even if the source was PNG/GIF/etc.
        pixbuf.savev(destination, 'jpeg', ['quality'], ['95'])

    def _is_jpeg_file(self, filename):
        try:
            with open(filename, 'rb') as fp:
                header = fp.read(3)
            return header.startswith(b'\xff\xd8')
        except Exception:
            return False

    def _store_manual_podcast_cover(self, podcast, cover_url='', cover_file=''):
        """Store manual podcast cover art locally as folder.jpg.

        Priority:
            1. Cover Art URL, if specified
            2. Selected local JPG file, if specified
            3. No change
        """

        cover_url = (cover_url or '').strip()
        cover_file = (cover_file or '').strip()

        if not cover_url and not cover_file:
            return

        save_dir = podcast.get_save_dir()
        destination = os.path.join(save_dir, 'folder.jpg')

        self._backup_existing_folder_jpg(destination)

        if cover_url:
            self._download_cover_url_to_folder_jpg(cover_url, destination)
        else:
            self._copy_local_cover_to_folder_jpg(cover_file, destination)

        podcast.cover_thumb = None
        podcast.save()
        self.ui.db.commit()

        self.ui.podcast_list_model.clear_cover_cache(podcast.url)

    #---------------------------------------------------------------------------
    # Private Methods - General Helper Functions
    #---------------------------------------------------------------------------
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
