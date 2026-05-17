# -*- coding: utf-8 -*-
#RobL-v-v-v-v-v-v-v-v-v-v-#-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-v-
#
#   podcastmetadata.py - New gPodder+ module added by RobL with help from ChatGPT
#
#RobL-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-^-
#
# gPodder+ podcast metadata providers
#
# This module intentionally keeps external podcast metadata lookup separate
# from normal feed parsing and normal subscription updates.

import abc
import hashlib
import logging
import time
import urllib.parse
from io import BytesIO

import podcastparser

import gpodder
from gpodder import util

_ = gpodder.gettext
logger = logging.getLogger(__name__)


class PodcastMetadataError(Exception):
    pass


class PodcastMetadataNotConfigured(PodcastMetadataError):
    pass


class MetadataPodcast(object):
    def __init__(
            self,
            title=None,
            feed_url=None,
            website_url=None,
            description=None,
            image_url=None,
            author=None,
            language=None,
            categories=None,
            source=None,
            source_id=None,
            raw=None):
        self.title = title
        self.feed_url = feed_url
        self.website_url = website_url
        self.description = description
        self.image_url = image_url
        self.author = author
        self.language = language
        self.categories = categories or []
        self.source = source
        self.source_id = source_id
        self.raw = raw or {}


class MetadataEpisode(object):
    def __init__(
            self,
            title=None,
            url=None,
            link=None,
            description=None,
            published=None,
            duration=None,
            image_url=None,
            season=None,
            number=None,
            guid=None,
            source=None,
            source_id=None,
            raw=None):
        self.title = title
        self.url = url
        self.link = link
        self.description = description
        self.published = published
        self.duration = duration
        self.image_url = image_url
        self.season = season
        self.number = number
        self.guid = guid
        self.source = source
        self.source_id = source_id
        self.raw = raw or {}


class PodcastMetadataProvider(object, metaclass=abc.ABCMeta):
    name = 'metadata-provider'

    def is_configured(self):
        return True

    def search_podcasts(self, query, limit=25):
        raise NotImplementedError()

    def lookup_by_feed_url(self, feed_url):
        raise NotImplementedError()

    def get_episodes(self, podcast, limit=25):
        raise NotImplementedError()


class RSSFeedMetadataProvider(PodcastMetadataProvider):
    """
    Uses the podcast's own RSS/Atom feed.

    This is the authoritative source for subscribed podcasts and should remain
    the default source for normal gPodder updates.
    """

    name = 'rss'

    def _parse_feed_url(self, feed_url):
        response = util.urlopen(feed_url)

        if not response.ok:
            raise PodcastMetadataError(
                'Could not fetch feed: %s: %d %s' %
                (feed_url, response.status_code, response.reason)
            )

        feed = podcastparser.parse(feed_url, BytesIO(response.content))
        feed['url'] = feed_url
        return feed

    def lookup_by_feed_url(self, feed_url):
        feed = self._parse_feed_url(feed_url)

        return MetadataPodcast(
            title=feed.get('title'),
            feed_url=feed_url,
            website_url=feed.get('link'),
            description=feed.get('description'),
            image_url=feed.get('cover_url'),
            author=feed.get('author') or feed.get('itunes_author'),
            language=feed.get('language'),
            categories=feed.get('categories') or [],
            source=self.name,
            source_id=feed_url,
            raw=feed,
        )

    def get_episodes(self, podcast, limit=25):
        feed_url = podcast.feed_url if isinstance(podcast, MetadataPodcast) else podcast
        feed = self._parse_feed_url(feed_url)

        episodes = []
        for item in feed.get('episodes', [])[:limit]:
            episodes.append(MetadataEpisode(
                title=item.get('title'),
                url=item.get('url'),
                link=item.get('link'),
                description=item.get('description'),
                published=item.get('published'),
                duration=item.get('total_time'),
                image_url=item.get('episode_art_url'),
                season=item.get('season'),
                number=item.get('number'),
                guid=item.get('guid'),
                source=self.name,
                source_id=item.get('guid') or item.get('url'),
                raw=item,
            ))

        return episodes

    def search_podcasts(self, query, limit=25):
        # RSS itself cannot search the web.
        return []


class PodcastIndexMetadataProvider(PodcastMetadataProvider):
    """
    Podcast Index provider.

    Requires:
        podcast_index.api_key
        podcast_index.api_secret

    Do not hard-code credentials in source.
    """

    name = 'podcastindex'
    BASE_URL = 'https://api.podcastindex.org/api/1.0'

    def __init__(self, api_key=None, api_secret=None, user_agent=None):
        self.api_key = api_key
        self.api_secret = api_secret
        self.user_agent = user_agent or 'gPodder+/1.0'

    def is_configured(self):
        return bool(self.api_key and self.api_secret)

    def _headers(self):
        if not self.is_configured():
            raise PodcastMetadataNotConfigured(
                'Podcast Index API key/secret are not configured'
            )

        auth_date = str(int(time.time()))
        auth_hash = hashlib.sha1(
            (self.api_key + self.api_secret + auth_date).encode('utf-8')
        ).hexdigest()

        return {
            'User-Agent': self.user_agent,
            'X-Auth-Key': self.api_key,
            'X-Auth-Date': auth_date,
            'Authorization': auth_hash,
        }

    def _get_json(self, path, params=None):
        params = params or {}
        query = urllib.parse.urlencode(params)
        url = self.BASE_URL + path
        if query:
            url += '?' + query

        response = util.urlopen(url, headers=self._headers())

        if not response.ok:
            raise PodcastMetadataError(
                'Podcast Index request failed: %s: %d %s' %
                (url, response.status_code, response.reason)
            )

        return response.json()

    def _podcast_from_feed(self, feed):
        categories = feed.get('categories') or {}
        if isinstance(categories, dict):
            categories = list(categories.values())

        return MetadataPodcast(
            title=feed.get('title'),
            feed_url=feed.get('url') or feed.get('originalUrl'),
            website_url=feed.get('link'),
            description=feed.get('description'),
            image_url=feed.get('image') or feed.get('artwork'),
            author=feed.get('author') or feed.get('ownerName'),
            language=feed.get('language'),
            categories=categories,
            source=self.name,
            source_id=feed.get('id'),
            raw=feed,
        )

    def _episode_from_item(self, item):
        return MetadataEpisode(
            title=item.get('title'),
            url=item.get('enclosureUrl'),
            link=item.get('link'),
            description=item.get('description'),
            published=item.get('datePublished') or item.get('datePublishedPretty'),
            duration=item.get('duration'),
            image_url=item.get('image') or item.get('feedImage'),
            season=item.get('season'),
            number=item.get('episode'),
            guid=item.get('guid'),
            source=self.name,
            source_id=item.get('id'),
            raw=item,
        )

    def search_podcasts(self, query, limit=25):
        data = self._get_json('/search/byterm', {
            'q': query,
            'max': limit,
        })

        return [
            self._podcast_from_feed(feed)
            for feed in data.get('feeds', [])
        ]

    def lookup_by_feed_url(self, feed_url):
        data = self._get_json('/podcasts/byfeedurl', {
            'url': feed_url,
        })

        feed = data.get('feed')
        if not feed:
            return None

        return self._podcast_from_feed(feed)

    def get_episodes(self, podcast, limit=25):
        if not isinstance(podcast, MetadataPodcast):
            raise PodcastMetadataError('Podcast Index episodes require a MetadataPodcast')

        if podcast.source_id is None:
            # Fall back to lookup by feed URL.
            podcast = self.lookup_by_feed_url(podcast.feed_url)

        if podcast is None or podcast.source_id is None:
            return []

        data = self._get_json('/episodes/byfeedid', {
            'id': podcast.source_id,
            'max': limit,
        })

        return [
            self._episode_from_item(item)
            for item in data.get('items', [])
        ]


class AppleITunesSearchMetadataProvider(PodcastMetadataProvider):
    """
    Apple iTunes Search provider.

    Useful as a fallback discovery provider. Do not treat it as the primary
    metadata authority for subscribed podcasts.
    """

    name = 'apple-itunes'
    SEARCH_URL = 'https://itunes.apple.com/search'
    LOOKUP_URL = 'https://itunes.apple.com/lookup'

    def _get_json(self, base_url, params):
        url = base_url + '?' + urllib.parse.urlencode(params)
        response = util.urlopen(url)

        if not response.ok:
            raise PodcastMetadataError(
                'Apple iTunes request failed: %s: %d %s' %
                (url, response.status_code, response.reason)
            )

        return response.json()

    def _podcast_from_result(self, result):
        return MetadataPodcast(
            title=result.get('collectionName') or result.get('trackName'),
            feed_url=result.get('feedUrl'),
            website_url=result.get('collectionViewUrl') or result.get('trackViewUrl'),
            description=result.get('description'),
            image_url=(
                result.get('artworkUrl600') or
                result.get('artworkUrl100') or
                result.get('artworkUrl60')
            ),
            author=result.get('artistName'),
            language=None,
            categories=[result.get('primaryGenreName')] if result.get('primaryGenreName') else [],
            source=self.name,
            source_id=result.get('collectionId') or result.get('trackId'),
            raw=result,
        )

    def _episode_from_result(self, result):
        return MetadataEpisode(
            title=result.get('trackName'),
            url=result.get('episodeUrl') or result.get('previewUrl'),
            link=result.get('trackViewUrl'),
            description=result.get('description'),
            published=result.get('releaseDate'),
            duration=result.get('trackTimeMillis'),
            image_url=(
                result.get('artworkUrl600') or
                result.get('artworkUrl100') or
                result.get('artworkUrl60')
            ),
            season=result.get('seasonNumber'),
            number=result.get('episodeNumber'),
            guid=None,
            source=self.name,
            source_id=result.get('trackId'),
            raw=result,
        )

    def search_podcasts(self, query, limit=25):
        data = self._get_json(self.SEARCH_URL, {
            'term': query,
            'media': 'podcast',
            'entity': 'podcast',
            'limit': limit,
        })

        return [
            self._podcast_from_result(item)
            for item in data.get('results', [])
        ]

    def lookup_by_feed_url(self, feed_url):
        # Apple has no reliable direct lookup-by-feed-url endpoint.
        # Search by URL as a fallback, then match exact feedUrl when present.
        results = self.search_podcasts(feed_url, limit=25)

        for podcast in results:
            if podcast.feed_url == feed_url:
                return podcast

        return None

    def get_episodes(self, podcast, limit=25):
        if not isinstance(podcast, MetadataPodcast) or podcast.source_id is None:
            return []

        data = self._get_json(self.LOOKUP_URL, {
            'id': podcast.source_id,
            'media': 'podcast',
            'entity': 'podcastEpisode',
            'limit': limit,
        })

        episodes = []
        for item in data.get('results', []):
            if item.get('wrapperType') == 'track' or item.get('kind') == 'podcast-episode':
                episodes.append(self._episode_from_result(item))

        return episodes


class PodcastMetadataService(object):
    """
    Ordered metadata service.

    Suggested order:
        1. RSS
        2. Podcast Index
        3. Apple iTunes Search
    """

    def __init__(self, providers=None):
        self.providers = providers or []

    def search_podcasts(self, query, limit=25):
        results = []

        for provider in self.providers:
            if not provider.is_configured():
                continue

            try:
                results.extend(provider.search_podcasts(query, limit))
            except Exception:
                logger.warning('Metadata provider failed: %s', provider.name, exc_info=True)

        return self._dedupe_podcasts(results)[:limit]

    def lookup_by_feed_url(self, feed_url):
        for provider in self.providers:
            if not provider.is_configured():
                continue

            try:
                result = provider.lookup_by_feed_url(feed_url)
                if result is not None:
                    return result
            except Exception:
                logger.warning('Metadata provider failed: %s', provider.name, exc_info=True)

        return None

    def get_episodes(self, podcast, limit=25):
        for provider in self.providers:
            if not provider.is_configured():
                continue

            try:
                episodes = provider.get_episodes(podcast, limit)
                if episodes:
                    return episodes
            except Exception:
                logger.warning('Metadata provider failed: %s', provider.name, exc_info=True)

        return []

    def _dedupe_podcasts(self, podcasts):
        result = []
        seen = set()

        for podcast in podcasts:
            key = podcast.feed_url or podcast.website_url or podcast.title
            if not key:
                continue

            key = key.strip().lower()
            if key in seen:
                continue

            seen.add(key)
            result.append(podcast)

        return result

# Module-level helper function
def create_metadata_service(config, include_rss=True):
    providers = []

    if include_rss:
        providers.append(RSSFeedMetadataProvider())

    try:
        if config.metadata.podcast_index.enabled:
            providers.append(PodcastIndexMetadataProvider(
                api_key=config.metadata.podcast_index.api_key,
                api_secret=config.metadata.podcast_index.api_secret,
                user_agent='gPodder+/1.0',
            ))
    except AttributeError:
        logger.warning('Podcast Index metadata config is missing', exc_info=True)

    try:
        if config.metadata.apple_itunes.enabled:
            providers.append(AppleITunesSearchMetadataProvider())
    except AttributeError:
        logger.warning('Apple iTunes metadata config is missing', exc_info=True)
        providers.append(AppleITunesSearchMetadataProvider())

    return PodcastMetadataService(providers)
