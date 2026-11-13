// Readable list of the deviations of this edition from the printed book
// (corrections.json), built as a separate PDF. An entry prints its id, the
// printed page, the place, the printed reading, the correction and the
// reason; `verified_by` (how the correction was checked) stays in the
// journal.
//
// The fields are Typst markup evaluated with the book's definitions; they
// quote numbers as printed, since the book's labels are not in this
// document.
#import "main-defs.typ" as defs
#import "book-style.typ": text-math-rules

#let scope = dictionary(defs)
#let entries = json("../corrections.json").entries
#let markup(field) = eval(field, mode: "markup", scope: scope)

#set document(
  title: "Теория рекурсивных функций и эффективная вычислимость. Исправления",
  author: "Х. Роджерс",
  date: none,
)
#set page(
  width: 145mm,
  height: 215mm,
  margin: (x: 15mm, top: 18mm, bottom: 20mm),
  footer: context align(center, text(size: 10pt, counter(page).display())),
)
#set text(font: "New Computer Modern", size: 10pt, lang: "ru")
#set par(justify: true, leading: 0.55em, spacing: 0.8em)
#show: text-math-rules

#align(center, text(size: 14pt, weight: "bold")[Исправления])

Х.~Роджерс, _Теория рекурсивных функций и эффективная вычислимость_. Перевод с
английского под ред. В.~А.~Успенского. Москва: Мир,~1972. В нашем издании
исправлены перечисленные ниже опечатки и ошибки; страницы указаны по печатной
книге, номера утверждений и формул совпадают с книгой.

// The entries go by the page of the book, grouped under the section they
// belong to, with a heading and a bookmark for each; an entry names its own
// place only where it is narrower than the section.
#show heading: set text(size: 12pt, hyphenate: false)
#show heading: set block(above: 1.6em, below: 0.8em)

#{
  let section = none
  for entry in entries {
    if entry.section != section {
      section = entry.section
      heading(level: 1, markup(section))
    }
    block(width: 100%, breakable: false, above: 1em)[
      #metadata((correction: entry.id))
      *#entry.id* · с.~#entry.printed_page#if (
        entry.place != entry.section
      ) [, #markup(entry.place)]

      // A long formula breaks only at its relations and operators: the
      // readings are ragged right, so that a line before such a break is not
      // stretched, and the labels are not hyphenated.
      #par(justify: false)[#box[Было:] #markup(entry.original)]

      #par(justify: false)[#box[Стало:] #markup(entry.corrected)]

      #text(size: 10pt, markup(entry.reason))
    ]
  }
}
