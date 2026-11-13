"""The alphabetical index: elements shared with the entry before become
dashes, the English term follows the entry, a pair of marks gives a range of
pages, a footnote «прим.», cross-references «см. также»."""
from pathlib import Path
import subprocess
import tempfile
import unittest

import pymupdf

ROOT = Path(__file__).resolve().parents[2]


class Index(unittest.TestCase):
    def test_entries_as_printed(self):
        source = '''#import "/content/book-style.typ": book-style
#import "/content/main-defs.typ": idx, notation
#show: book-style
#counter(page).update(10)
Первая.#idx("Аналитическая", "иерархия", en: "analytical hierarchy",
  range: "start")#idx("Алгоритм", ", неформальное понятие", en: "algorithm")
#notation($phi_x$)
#pagebreak()
Вторая.#idx("Аналитическая", "иерархия", "теорема о полноте",
  en: "completeness theorem")#idx("Алгоритм", "нечисловой", en:
  "non-numerical")#footnote[Сноска.#idx("Кантор", en: "Cantor G.", note:
  true)]
#pagebreak()
Третья.#idx("Аналитическая", "иерархия", en: "analytical hierarchy",
  range: "end")#idx("Аналитические множества", en: "analytical sets",
  see-also: "Аналитическая иерархия")
#include "/content/90-index.typ"
'''
        with tempfile.TemporaryDirectory(prefix='rogers-index-', dir='/tmp') as d:
            path = Path(d) / 'index.pdf'
            result = subprocess.run([
                'typst', 'compile', '--root', str(ROOT),
                '--font-path', str(ROOT / 'assets/fonts'),
                '--ignore-system-fonts', '-', str(path),
            ], input=source, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stderr, '')
            with pymupdf.open(path) as pdf:
                text = ' '.join(' '.join(p.get_text().split()) for p in pdf)
                text = text.replace('⁠', '')
            self.assertIn('Алгоритм, неформальное понятие (algorithm) 10', text)
            self.assertIn('— нечисловой (non-numerical) 11', text)
            self.assertIn('Аналитическая иерархия (analytical hierarchy) 10—12',
                          text)
            self.assertIn('— — теорема о полноте (completeness theorem) 11',
                          text)
            self.assertIn('Аналитические множества (analytical sets) 12; см. '
                          'также Аналитическая иерархия', text)
            self.assertIn('Кантор (Cantor G.) 11 прим.', text)

    def test_greek_after_cyrillic(self):
        """As in the book: Я, then Δ, λ, μ, ω of formulas, then Latin."""
        source = '''#import "/content/book-style.typ": book-style
#import "/content/main-defs.typ": idx
#show: book-style
Текст.#idx("btt-сводимость", en: "btt-reducibility")#idx("$omega$-скачок",
  en: "omega-jump")#idx("$mu$-оператор", en: "mu operator")#idx(
  "$Delta^1_1$-множество", en: "Delta set")#idx("Ячейка", en:
  "cell")#idx("$lambda$-обозначение", en: "lambda notation")
#include "/content/90-index.typ"
'''
        with tempfile.TemporaryDirectory(prefix='rogers-index-', dir='/tmp') as d:
            path = Path(d) / 'index.pdf'
            result = subprocess.run([
                'typst', 'compile', '--root', str(ROOT),
                '--font-path', str(ROOT / 'assets/fonts'),
                '--ignore-system-fonts', '-', str(path),
            ], input=source, text=True, capture_output=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            with pymupdf.open(path) as pdf:
                text = ' '.join(' '.join(p.get_text().split()) for p in pdf)
                text = text.replace('⁠', '')
            order = [text.rindex(f'({term})') for term in (
                'cell', 'Delta set', 'lambda notation', 'mu operator',
                'omega-jump', 'btt-reducibility')]
            self.assertEqual(order, sorted(order))


if __name__ == '__main__':
    unittest.main()
