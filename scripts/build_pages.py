#!/usr/bin/env python3
"""Assemble the checked blueprint and PDF for GitHub Pages."""

from functools import cache
from html.parser import HTMLParser
from pathlib import Path
import shutil
import subprocess
import sys
from urllib.parse import unquote, urlsplit

from manuscript_map import lean_locations, lean_source_urls


ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / '_site'
BLUEPRINT = ROOT / 'blueprint/web'
PDF = ROOT / 'blueprint/print/print.pdf'


class Page(HTMLParser):
    def __init__(self, path):
        super().__init__()
        self.ids = set()
        self.links = []
        self.feed(path.read_text(encoding='utf-8'))

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if 'id' in attrs:
            self.ids.add(attrs['id'])
        if tag == 'a' and 'href' in attrs:
            self.links.append((attrs['href'], attrs.get('class', '').split()))


@cache
def page(path):
    return Page(path)


def check_local_link(base, href):
    base = base.resolve()
    url = urlsplit(href)
    # Leading / paths would incorrectly escape this repository's Pages prefix.
    if url.scheme or url.netloc or url.path.startswith('/'):
        raise ValueError(f'Expected a relative documentation link: {href}')
    target = (base / unquote(url.path)).resolve()
    if target.is_dir():
        target /= 'index.html'
    if not target.is_relative_to(base) or not target.is_file():
        raise ValueError(f'Missing local documentation target: {href}')
    if url.fragment and unquote(url.fragment) not in page(target).ids:
        raise ValueError(f'Missing documentation anchor: {href}')


def check_source_links():
    names = set((ROOT / 'blueprint/lean_decls').read_text().splitlines()) - {''}
    if not names:
        raise ValueError('No blueprint Lean declarations to check.')
    expected = set(lean_source_urls(names).values())
    linked = set()
    for path in BLUEPRINT.glob('*.html'):
        for href, classes in page(path).links:
            if 'lean_decl' not in classes:
                continue
            if href not in expected:
                raise ValueError(f'Unexpected blueprint Lean source link: {href}')
            linked.add(href)
    if linked != expected:
        raise ValueError('Rendered Lean source links differ from blueprint/lean_decls.')

    # Published line anchors must describe the pinned commit, not local edits.
    # Local blueprint previews remain available before committing proof changes.
    locations = lean_locations()
    source_files = {locations[name][0] for name in names}
    changed = set(subprocess.check_output(
        ['git', 'diff', '--name-only', 'HEAD', '--', 'GaussianTesting'],
        cwd=ROOT, text=True).splitlines())
    changed.update(subprocess.check_output(
        ['git', 'ls-files', '--others', '--exclude-standard', '--', 'GaussianTesting'],
        cwd=ROOT, text=True).splitlines())
    if dirty := source_files & changed:
        raise ValueError('Commit Lean source changes before assembling the publishable site: '
                         + ', '.join(sorted(dirty)))
    print(f'Checked {len(names)} blueprint declarations against commit-pinned source files and lines.')


def main():
    # Fail before touching an existing site if any required build is incomplete.
    required = [
        ROOT / 'blueprint/lean_decls', PDF,
        BLUEPRINT / 'index.html', BLUEPRINT / 'sec-manuscript-index.html',
        BLUEPRINT / 'dep_graph_document.html', BLUEPRINT / 'dep_graph_wide.html',
    ]
    for path in required:
        if not path.is_file() or path.stat().st_size == 0:
            sys.exit(f'Missing documentation output: {path.relative_to(ROOT)}')

    check_source_links()

    # This directory contains generated output only; recreate it to avoid
    # publishing obsolete pages left behind by an earlier local build.
    if SITE.exists():
        shutil.rmtree(SITE)
    shutil.copytree(BLUEPRINT, SITE)
    shutil.copyfile(PDF, SITE / 'blueprint.pdf')
    local_links = 0
    for href, _ in page(SITE / 'index.html').links:
        url = urlsplit(href)
        if not url.scheme and not url.netloc:
            check_local_link(SITE, href)
            local_links += 1
    site_bytes = sum(path.stat().st_size for path in SITE.rglob('*') if path.is_file())
    if site_bytes > 1_000_000_000:
        raise ValueError('Assembled site exceeds GitHub Pages\' 1 GB published-site limit.')
    print(f'Checked {local_links} local blueprint homepage links in the assembled site.')
    print(f'Assembled blueprint at the site root, with blueprint.pdf ({site_bytes / 1_000_000:.1f} MB).')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError) as error:
        sys.exit(str(error))
