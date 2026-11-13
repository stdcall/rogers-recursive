"""Compile the shared styles and inspect the actual numbered records."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class Numbering(unittest.TestCase):
    def test_book_scheme(self):
        # Theorems are numbered in roman numerals through their chapter, a
        # corollary carries the number of the theorem before it, exercises
        # count in arabic numerals through the chapter. A reference prints the
        # own number in the chapter of its target and «chapter-number»
        # outside it; a section prints «1.2», a named point its symbol.
        source = '''#import "/content/book-style.typ": book-style
#import "/content/main-defs.typ": *
#import "/content/statements.typ": *
#show: book-style
#chapter[Первая] <ch:first>
#section[Первый] <sec:first>
#point("*1")[Пункт.] <ax:first>
#theorem[Теорема.] <th:first>
#corollary[Следствие.] <cor:first>
#theorem[Теорема.] <th:second>
#corollary[Следствие.] <cor:second>
#corollary(suffix: " (b)")[Следствие.] <cor:second-b>
#lemma[Лемма.] <lem:plain>
#lemma(numbered: true, number: 2)[Лемма.] <lem:two>
#section[Второй] <sec:second>
#theorem[Теорема.] <th:third>
#corollary(base: "th:first")[Следствие.] <cor:of-first>
Ссылки: @th:second, @cor:second, @cor:second-b, @lem:two, @ax:first,
§~@sec:second, @cor:of-first.
#chapter[Вторая] <ch:second>
#section[Третий] <sec:third>
#theorem[Теорема.] <th:fourth>
#section[Упражнения] <sec:exercises>
#exercise[Упражнение.] <ex:one>
#exercise(mark: "open")[Упражнение.] <ex:two>
Ссылки: @th:third, @th:fourth, @ex:two, гл.~@ch:first, §~@sec:first.
'''
        with tempfile.TemporaryDirectory(prefix='rogers-', dir='/tmp') as d:
            driver = Path(d) / 'driver.typ'
            driver.write_text(source)
            result = subprocess.run([
                'typst', 'eval', '--root', str(ROOT),
                '--font-path', str(ROOT / 'assets/fonts'),
                '--ignore-system-fonts',
                'query(metadata).map(it => it.value)',
                '--in', '-', '--format', 'json',
            ], input=source, capture_output=True, text=True, cwd=ROOT)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            records = json.loads(result.stdout)
            numbered = [(r['family'], r['number']) for r in records
                        if isinstance(r, dict) and r.get('kind') == 'numbered']
            self.assertEqual([n for f, n in numbered if f == 'th'],
                             [[1, 'I'], [1, 'II'], [1, 'III'], [2, 'I']])
            self.assertEqual([n for f, n in numbered if f == 'cor'],
                             [[1, 'I'], [1, 'II'], [1, 'II (b)'], [1, 'I']])
            self.assertEqual([n for f, n in numbered if f == 'ex'],
                             [[2, 1], [2, 2]])
            refs = [r for r in records if isinstance(r, dict)
                    and r.get('kind') == 'cross-reference']
            self.assertEqual([r['printed'] for r in refs], [
                'II', 'II', 'II (b)', '2', '*1', '1.2', 'I',
                '1-III', 'I', '2', '1', '1.1',
            ])
            self.assertTrue(all(r['resolved'] for r in refs))


if __name__ == '__main__':
    unittest.main()
