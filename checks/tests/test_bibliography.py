"""The bibliography through the actual compiler: descriptions come from
references.bib only, mentions in the text and in footnotes give the page
list of a work, the bibliography's own text does not, and the label of a
work is its year, with a letter after the first work of the same year in
the group ("[1970]", "[1970a]") and a star after a work added in the
translation ("[1971]*")."""
from pathlib import Path
import json
import re
import shutil
import subprocess
import tempfile
import unittest

import pymupdf

ROOT = Path(__file__).resolve().parents[2]

FIXTURE = '''@article{Probe1964,
  author = {Original, A. and Second, B. B.},
  authorru = {Оригинал and Второй},
  title = {Original title with $p$-groups},
  journal = {Original Journal of Mathematics},
  shortjournal = {Orig. J. Math.},
  volume = {37},
  year = {1964},
  pages = {100--125},
  doi = {10.1234/original-probe},
  language = {english},
  related = {Related1965},
  annotation = {{title}, {journal}, {volume} ({year}), {pages}; русский
    перевод: {Related1965.author}, {Related1965.title}, {Related1965.year}.},
}

@book{Related1965,
  author = {Переводчиков, П. П.},
  title = {Переведенное заглавие},
  year = {1965},
  language = {russian},
}

@article{Other1970,
  author = {Другой, Д. Д.},
  nameaddon = {Прежняя},
  title = {Другая работа},
  journal = {Другой журнал},
  volume = {1},
  year = {1970},
  pages = {1--2},
  annotation = {{title}, {journal}, {volume} ({year}), {pages}.},
}
'''

HEAD = ('#import "content/book-style.typ": book-style\n'
        '#import "content/bibliography-style.typ": bib-group, bib-item, '
        'bib-preface\n'
        '#show: book-style\n'
        '#set page(header: none, footer: none)\n')


class Fixture:
    def __init__(self, tmp, sample, data=FIXTURE):
        self.root = Path(tmp)
        shutil.copytree(ROOT/'content', self.root/'content')
        shutil.copytree(ROOT/'assets/fonts', self.root/'assets/fonts')
        (self.root/'editorial.bib').write_text('')
        self.write(data)
        (self.root/'sample.typ').write_text(HEAD + sample)
        self.args = ['--root', str(self.root), '--ignore-system-fonts',
                     '--font-path', str(self.root/'assets/fonts')]

    def write(self, data):
        (self.root/'references.bib').write_text(data)

    def compile(self, test, name='sample.pdf'):
        result = subprocess.run(
            ['typst', 'compile', *self.args, str(self.root/'sample.typ'),
             str(self.root/name)], capture_output=True, text=True)
        test.assertEqual(result.returncode, 0, result.stderr)
        test.assertEqual(result.stderr, '', result.stderr)
        return pymupdf.open(self.root/name)

    def query(self, test, expression):
        result = subprocess.run(
            ['typst', 'eval', *self.args, expression, '--in',
             str(self.root/'sample.typ'), '--format', 'json'],
            capture_output=True, text=True)
        test.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(result.stdout)


def page_text(doc):
    text = ' '.join(' '.join(page.get_text().split()) for page in doc)
    # Soft hyphens and word joiners (around page ranges) are invisible.
    return re.sub(r'­\s*', '', text).replace('\u2060', '')


def squeezed(text):
    """The text without spaces: spaced-out surnames come back whole."""
    return re.sub(r'\s+', '', text)


class BibliographySource(unittest.TestCase):
    def test_data_changes_reach_text_and_links(self):
        sample = ('#bib-group("Probe1964")\n'
                  '#bib-item("Probe1964") <bib:Probe1964>\n')
        with tempfile.TemporaryDirectory(prefix='rogers-bib-') as tmp:
            fixture = Fixture(tmp, sample)

            def build(name):
                with fixture.compile(self, name) as doc:
                    links = {link['uri'] for page in doc
                             for link in page.get_links() if 'uri' in link}
                    return page_text(doc), links

            before, old_links = build('before.pdf')
            for phrase in ('Original title with', 'Orig. J. Math.',
                           '37 (1964), 100–125', 'Переведенное заглавие',
                           'DOI: 10.1234/original'):
                self.assertIn(phrase, before)
            self.assertNotIn('Original Journal of Mathematics', before)
            for phrase in ('Оригинал,Второй(OriginalA.,SecondB.B.)',
                           'ПереводчиковП.П.'):
                self.assertIn(phrase, squeezed(before))
            self.assertIn('https://doi.org/10.1234/original-probe', old_links)

            changed = (FIXTURE
                       .replace('Original title', 'Changed title')
                       .replace('shortjournal = {Orig. J. Math.}',
                                'shortjournal = {Chg. J. Math.}')
                       .replace('year = {1964}', 'year = {1966}')
                       .replace('100--125', '9001--9002')
                       .replace('original-probe', 'changed-probe')
                       .replace('Original, A.', 'Renamed, A.'))
            fixture.write(changed)
            after, new_links = build('after.pdf')
            for phrase in ('Changed title with', 'Chg. J. Math.',
                           '[1966]', '37 (1966), 9001–',
                           'DOI: 10.1234/changed'):
                self.assertIn(phrase, after)
            for phrase in ('Original title', 'Orig. J. Math.', '1964',
                           '100–125', '10.1234/original'):
                self.assertNotIn(phrase, after)
            self.assertIn('(RenamedA.,SecondB.B.)', squeezed(after))
            self.assertIn('https://doi.org/10.1234/changed-probe', new_links)
            self.assertNotIn('https://doi.org/10.1234/original-probe',
                             new_links)

    def test_mentions_in_text_and_footnotes_only(self):
        sample = ('Mention in the text: Оригинал~@bib:Probe1964.\n'
                  '#pagebreak()\n'
                  'A page with a footnote.#footnote[Mention in a footnote: '
                  '@bib:Probe1964.]\n'
                  '#pagebreak()\n'
                  'Two mentions on one page: @bib:Probe1964 and '
                  '@bib:Probe1964.\n'
                  '#pagebreak()\n'
                  '#heading(level: 1, numbering: none)[Литература]\n'
                  '#bib-preface[The list cites itself: @bib:Probe1964, '
                  '@bib:Other1970.]\n'
                  '#bib-group("Probe1964")\n'
                  '#bib-item("Probe1964") <bib:Probe1964>\n'
                  '#bib-group("Other1970")\n'
                  '#bib-item("Other1970") <bib:Other1970>\n')
        with tempfile.TemporaryDirectory(prefix='rogers-bib-mentions-') as tmp:
            fixture = Fixture(tmp, sample)
            with fixture.compile(self) as doc:
                text = page_text(doc[3:])
                targets = [link['page'] for link in doc[3].get_links()
                           if link.get('kind') == pymupdf.LINK_GOTO]
            mentions = fixture.query(
                self, 'query(metadata).map(it => it.value).filter(it => '
                'type(it) == dictionary and '
                'it.at("kind", default: none) == "page-reference")')
            pages = {}
            for mention in mentions:
                pages.setdefault(mention['target'], []).append(
                    mention['target-position']['page'])
            # Pages 1, 2 (the footnote) and 3 (once), not the list itself.
            self.assertEqual(pages, {'bib-mention:bib:Probe1964': [1, 2, 3]})
            self.assertIn('[с. 1, 2, 3]', text)
            self.assertIn('ДругойД.Д.', squeezed(text))
            for page in (0, 1, 2):
                self.assertIn(page, targets)

    def test_year_labels_and_stars(self):
        sample = ('#heading(level: 1, numbering: none)[Литература]\n'
                  '#bib-group("Probe1964")\n'
                  '#bib-item("Probe1964") <bib:Probe1964>\n'
                  '#bib-group("Other1970")\n'
                  '#bib-item("Other1970") <bib:Other1970>\n'
                  '#bib-item("Other1970a") <bib:Other1970a>\n'
                  '#bib-item("Third1971") <bib:Third1971>\n'
                  '#bib-item("Fourth1972", label: "1972b") <bib:Fourth1972>\n'
                  'In the text: @bib:Other1970a, @bib:Third1971, '
                  '@bib:Fourth1972.\n')
        extra = ''
        for key, name, title, year, star in (
                ('Other1970a', 'Другой, Д. Д.', 'Вторая', 1970, False),
                ('Third1971', 'Другой, Д. Д.', 'Третья', 1971, True),
                ('Fourth1972', 'Другой, Д. Д.', 'Четвертая', 1972, False)):
            extra += (f'\n@article{{{key},\n  author = {{{name}}},\n'
                      f'  title = {{{title}}},\n  year = {{{year}}},\n'
                      + ('  keywords = {translation},\n' if star else '')
                      + '  annotation = {{title}, {year}.},\n}\n')
        with tempfile.TemporaryDirectory(prefix='rogers-bib-labels-') as tmp:
            fixture = Fixture(tmp, sample, FIXTURE + extra)
            with fixture.compile(self) as doc:
                text = page_text(doc)
            numbers = fixture.query(
                self, 'query(<numbered>).map(it => it.value).filter(it => '
                'it.at("family", default: none) == "bib")'
                '.map(it => it.number)')
            self.assertEqual(numbers, [['1964'], ['1970'], ['1970a'],
                                       ['1971'], ['1972b']])
            self.assertIn('In the text: [1970a], [1971], [1972b].', text)
            self.assertIn('[1971]*', text)
            self.assertIn('ДругойД.Д.', squeezed(text))


if __name__ == '__main__':
    unittest.main()
