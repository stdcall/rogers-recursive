#set document(
  title: "Теория рекурсивных функций и эффективная вычислимость",
  author: "Х. Роджерс",
  date: none,
)
#import "book-style.typ": book-contents, book-style
#import "main-defs.typ": unnumbered-chapter
#import "frontmatter/cover.typ": cover
#import "frontmatter/title.typ": imprint-page, original-title-page, title-page
#cover()
#show: book-style
#counter(page).update(2)
#original-title-page()
#title-page()
#imprint-page()
#include "00-front.typ"
#include "01-01-algorithms.typ"
#include "01-02-primitive-recursive.typ"
#include "01-08-goedel-numbers.typ"
#include "02-01-unsolvable-problems.typ"
#include "03-01-purposes.typ"
#include "05-01-recursive-sets.typ"
#include "06-01-reducibilities.typ"
#include "07-07-productiveness.typ"
#include "08-01-truth-table.typ"
#include "09-01-turing-reducibility.typ"
#include "09-07-enumeration-reducibility.typ"
#include "10-01-post-problem.typ"
#include "11-01-recursion-theorem.typ"
#include "11-06-ordinal-notations.typ"
#include "12-01-lattice.typ"
#include "12-06-almost-finiteness.typ"
#include "13-01-jump.typ"
#include "13-04-ordering-degrees.typ"
#include "13-08-further-results.typ"
#include "14-01-arithmetical-hierarchy.typ"
#include "14-06-degrees.typ"
#include "15-01-classes-of-sets.typ"
#include "15-02-classes-of-functions.typ"
#include "15-03-functionals.typ"
#include "16-01-analytical-hierarchy.typ"
#include "16-03-well-founded-trees.typ"
#include "16-06-hyperdegrees.typ"
#include "16-07-basis-results.typ"
#include "16-08-hyperarithmetical.typ"
#include "80-bibliography.typ"
#include "90-index.typ"
#unnumbered-chapter(outlined: false)[Оглавление]
#book-contents
