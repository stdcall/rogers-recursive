#import "numbering.typ": (
  chapter-of, family-counter, numbered-record, place-key, printed-number,
  record, record-number, reset-numbering, statement-families,
)

// `#source(n)`: the place where printed page n of the book begins; the page of
// the file is the printed page.
#let source(n) = [#metadata((
  kind: "source",
  file-page: n,
  printed-page: str(n),
))]

// Numbers are semibold in references, but never lighter than a bold heading
// around them, and never letterspaced with their head. New Computer Modern has
// no semibold cut: a hairline stroke gives its weight.
#let number-text(body) = context {
  let weight = text.weight
  let heavy = (
    weight in ("bold", "extrabold", "black")
      or (type(weight) == int and weight > 600)
  )
  text(
    stroke: if heavy { none } else { 0.2pt + black },
    style: "normal",
    tracking: 0pt,
    body,
  )
}

// Keep a reference's invisible position with its first visible word.
// Descriptive references may wrap over several lines.
#let caption-link(body, destination) = {
  if type(body) == str { body = text(body) }
  if body.func() in ([ ].func(), linebreak, parbreak, h, v, metadata) {
    return body
  }
  if body.func() == text and body.has("text") {
    let visible = body.text.match(regex("\\S(?:[\\s\\S]*\\S)?"))
    if visible == none { return body }
    return [#body.text.slice(0, visible.start)#link(
        destination,
        body.text.slice(visible.start, visible.end),
      )#body.text.slice(visible.end)]
  }
  if body.func() == [].func() {
    return body.children.map(it => caption-link(it, destination)).join()
  }
  if body.func() in (emph, strong) {
    let fields = body.fields()
    let inner = fields.remove("body")
    return body.func()(caption-link(inner, destination), ..fields)
  }
  if body.func() == link { body } else { link(destination, body) }
}
#let anchor-caption(body, marker, destination) = {
  if body.func() in ([ ].func(), linebreak, parbreak, h, v, metadata) {
    return (false, body)
  }
  if body.func() == text and body.has("text") {
    let word = body.text.match(regex("\\S+"))
    if word == none { return (false, body) }
    return (
      true,
      [#body.text.slice(0, word.start)#box[
          #marker#link(destination, body.text.slice(word.start, word.end))
        ]#caption-link(body.text.slice(word.end), destination)],
    )
  }
  if body.func() == [].func() {
    let done = false
    let parts = ()
    for child in body.children {
      if done { parts.push(caption-link(child, destination)) } else {
        let (found, content) = anchor-caption(child, marker, destination)
        done = found
        parts.push(content)
      }
    }
    return (done, parts.join())
  }
  if body.func() in (emph, strong, link) {
    let fields = body.fields()
    let (found, content) = anchor-caption(
      fields.remove("body"),
      marker,
      destination,
    )
    return (found, body.func()(content, ..fields))
  }
  (true, box[#marker#link(destination, body)])
}

// A reference prints the number as the book does (numbering.typ): «VI» or
// «7-VI» for a theorem, «14» or «7-14» for an exercise, «7.4» for a section,
// «7» for a chapter, «[1959a]» for a work of the bibliography.
#let reference-body(
  it,
  caption,
  trace: true,
  bibliographic-mention: true,
) = context {
  let target = str(it.target)
  let prefix = target.split(":").first()
  // A citation takes its supplement as a place in the work, «[1951, стр.
  // 1—67]»; `[-]` prints the label alone, for cites().
  let locator = if prefix == "bib" and caption { it.supplement }
  // `@th:name-a[-]` names a theorem printed in parts as a whole: «X» for the
  // parts X (a) and X (b).
  let whole = caption and prefix != "bib" and it.supplement == [-]
  let caption = caption and prefix != "bib" and not whole
  let record = if it.element != none { numbered-record(it.target) }
  let number = if prefix in ("pg", "front") and it.element != none {
    (counter(page).at(it.element.location()).first(),)
  } else if record != none { record-number(record) }
  // A descriptive reference may name an unnumbered statement.
  let pending = number == none and not (caption and record != none)
  let printed = if number == none { "?" } else if prefix in ("sec", "ch") {
    number.map(str).join(".")
  } else { printed-number(number, chapter-of(here())) }
  let printed = if whole { printed.split(" (").first() } else { printed }
  let symbol = if record != none { record.value.at("symbol", default: none) }
  let body = if caption { it.supplement } else if (
    prefix == "eq" and symbol != none
  ) {
    text(style: "normal", tracking: 0pt)[(#number-text(symbol))]
  } else if prefix == "eq" {
    text(style: "normal", tracking: 0pt)[(#number-text(printed))]
  } else if prefix == "bib" and locator == [-] {
    text(style: "normal", tracking: 0pt, number-text(printed))
  } else if prefix == "bib" {
    text(style: "normal", tracking: 0pt)[\[#number-text(printed)#if (
        locator != none
      ) [, #locator]\]]
  } else if prefix == "ax" and not pending {
    // A named point prints its symbol.
    text(style: "normal", tracking: 0pt, number-text(record.value.symbol))
  } else { number-text(printed) }
  if not trace { return body }
  let destination = if pending { none } else if (
    prefix in ("pg", "front") or it.element.func() == math.equation
  ) { it.element.location() } else { record.location() }
  let marker = {
    metadata((
      kind: "cross-reference",
      target: target,
      resolved: not pending,
      printed: printed,
      target-location: destination,
    ))
    if prefix == "bib" {
      [#metadata((
        kind: "bibliography-mention",
        target: target,
        bibliographic-mention: bibliographic-mention,
      ))<bibliography-mention>]
    }
  }
  if caption and not pending {
    return anchor-caption(body, marker, destination).last()
  }
  let anchored = [#marker#body]
  if pending { anchored } else { link(destination, anchored) }
}

#let reference-rules(body, trace: true, bibliographic-mention: true) = {
  show ref: it => {
    let caption = it.supplement not in (auto, none, [], [°], [′])
    let shown = reference-body(
      it,
      caption,
      trace: trace,
      bibliographic-mention: bibliographic-mention,
    )
    // A descriptive reference may wrap; a number, also a citation with its
    // place, stays whole with its marker.
    let citation = str(it.target).starts-with("bib:")
    if caption and not citation and it.supplement != [-] { shown } else {
      [#sym.wj#box(shown)]
    }
  }
  body
}

// A mention of a work that the book describes in full where it cites it (a
// footnote of the prefaces): the printed description stays, and the place
// counts among the pages of the work in the bibliography. `#mention(<bib:Key>)`
// prints nothing.
#let mention(target) = [#metadata((
  kind: "bibliography-mention",
  target: str(target),
  bibliographic-mention: true,
))<bibliography-mention>]

// Several works of one author in one pair of brackets, «Эрбран [1931,
// 1931a]»: `Эрбрана #cites(<bib:Herbrand1931>, <bib:Herbrand1931a>)`.
#let cites(..labels) = {
  let refs = labels.pos().map(l => ref(l, supplement: [-]))
  [\[#refs.join[, ]\]]
}

// A place that the text calls by its page («см. с. 94»): `#page-mark <pg:…>`
// at the place, `с.~@pg:…` in the text.
#let page-mark = metadata((kind: "page-mark"))

// A mark of the alphabetical index at the place of its term: the path of the
// entry, «#idx("Функция", "универсальная", en: "universal function")», and the
// English term of the book's index after the last word (for a person, the
// name in Latin letters, «#idx("Пост", en: "Post E. L.")»). `target`: the
// label of the statement or heading the entry leads to. `range: "start"` and
// `range: "end"` with the same path give a range of pages, «478—586»; `note:
// true` marks a footnote, «498 прим.»; `see` and `see-also` give the
// cross-references of the entry, «см. также Аналитическая иерархия»;
// `qualifier` a word the book prints after the English term, «(logical
// notation) (Введение)».
#let idx(
  target: none,
  en: none,
  range: none,
  note: false,
  see: none,
  see-also: none,
  qualifier: none,
  ..path,
) = {
  assert(path.named().len() == 0 and path.pos().len() > 0)
  assert(range in (none, "start", "end"), message: "idx: range")
  [#metadata((
    kind: "index-mark",
    path: path.pos(),
    en: en,
    target: target,
    range: range,
    note: note,
    see: see,
    see-also: see-also,
    qualifier: qualifier,
  ))<index-mark>]
}

// A mark of the index of notations at the place where a sign is introduced:
// `#notation($phi_x$)`. The signs go by their pages and, on one page, by
// their places; `order: 1, 2, …` orders the signs of a page as the book does
// where that differs. `key` makes marks of one sign written differently one
// entry.
// `range: "start"` and `range: "end"` mark the pages of a sign the book gives
// as a range, «286—288».
#let notation(
  sign,
  key: none,
  order: none,
  target: none,
  range: none,
) = [#metadata((
  kind: "notation-mark",
  sign: sign,
  key: key,
  order: order,
  target: target,
  range: range,
))<notation-mark>]

#let editorial-note-counter = counter("editorial-note")
#let ed-note(body) = {
  editorial-note-counter.step()
  [#metadata("editorial-note")]
  context {
    // «*1)» in the text and in the note, a space before the note's text.
    let mark = "*" + str(editorial-note-counter.get().first()) + ")"
    footnote(numbering: _ => mark)[#body~— _Прим. ред._]
    counter(footnote).update(n => n - 1)
  }
}

// `short`: the title in the running head, where the book shortens it. It is
// kept in the supplement of the heading, which prints nowhere else.
#let running(title, short) = if short == none { title } else { short }
// A footnote of a title belongs to the printed title only: the heading, read
// by the bookmarks and the contents, takes the title without it. Hidden by a
// show rule, a footnote would still place its entry on the page.
#let without-notes(body) = {
  if type(body) != content { body } else if body.func() == footnote {
    []
  } else if body.func() == [].func() {
    body.children.map(without-notes).join()
  } else { body }
}
// The title of a chapter-like opening as printed, footnotes included, while
// its heading carries the title without them.
#let printed-title = state("printed-title", none)

// «Глава 1. РЕКУРСИВНЫЕ ФУНКЦИИ» on a new page, the list of its sections
// under it (book-style.typ).
#let chapter(title, short: none) = {
  pagebreak(weak: true)
  reset-numbering()
  let plain = without-notes(title)
  if plain != title { printed-title.update(title) }
  heading(level: 1, supplement: running(plain, short), plain)
  if plain != title { printed-title.update(none) }
}
// «§ 1.1. НЕФОРМАЛЬНОЕ ПОНЯТИЕ АЛГОРИТМА».
#let section(title, short: none) = {
  // The examples are numbered in each section.
  family-counter("exm").update(0)
  let plain = without-notes(title)
  if plain != title { printed-title.update(title) }
  heading(level: 2, supplement: running(plain, short), plain)
  if plain != title { printed-title.update(none) }
}

// A head inside a section on a line of its own, «Кодирования», «Формализация
// Тьюринга»: bold, flush left; in the bookmarks, not in the contents.
#let subheading(title) = heading(
  level: 3,
  numbering: none,
  outlined: false,
  bookmarked: true,
  title,
)

// An empty paragraph keeps the chain of paragraphs: the next one is indented
// after a display, a list or a heading, too. It takes no room of its own. The
// style puts it at each blank line of the source (book-style.typ), so that a
// blank line after a display opens a new paragraph and text without one goes
// on with the sentence from the margin.
#let new-paragraph = context {
  par(spacing: 0pt, sym.zws)
  v(-par.spacing - measure(sym.zws).height)
}

// The small type of the exercises.
#let petit-size = 8pt
#let petit(body) = {
  set text(size: petit-size)
  set par(leading: 0.44em, spacing: 0.44em)
  body
}

// The prefaces, the introduction, the bibliography, the indexes:
// chapter-like openings without a number. `outlined: false` keeps a title
// out of the contents.
#let unnumbered-chapter(
  title,
  outlined: true,
  short: none,
) = {
  pagebreak(weak: true)
  let plain = without-notes(title)
  if plain != title { printed-title.update(title) }
  heading(
    level: 1,
    numbering: none,
    outlined: outlined,
    supplement: running(plain, short),
    plain,
  )
  if plain != title { printed-title.update(none) }
}

// The index stands in two columns.
#let two-columns(body) = {
  set par(first-line-indent: 0pt, justify: false, leading: 0.45em)
  set text(size: 8pt)
  columns(2, gutter: 5mm, body)
}
#let subject-index = two-columns

// Bold letters of the book: upright `bf(N)`, italic `bi(x)`.
#let bf(body) = math.upright(math.bold(body))
#let bi(body) = math.italic(math.bold(body))
// Delimiters that grow with their contents, where the book prints them so
// (the style keeps delimiters at text size, as TeX does): `grow((1/n + x))`.
#let grow(body) = math.lr(body, size: 100%)
// An empty atom: a sign at the start of a row of a broken display stays binary,
// `& nil + d`.
#let nil = math.class("normal", box(width: 0pt))

// The zero and the unit of a lattice where the book prints them as italic
// digits, «нулевой элемент (0)»: `zero`, `one`.
#let zero = text(font: "New Computer Modern", style: "italic", "0")
#let one = text(font: "New Computer Modern", style: "italic", "1")

// A marker of a priority construction, its number in a frame: `marker(j)_2`.
// The frame has one size for every number, j and x_i too, and stands out of
// the line without spreading it.
#let marker(body) = box(
  height: 0.7em,
  inset: (x: 0.2em),
  outset: (top: 0.15em, bottom: 0.3em),
  stroke: 0.4pt,
  $body$,
)

// The Cartesian product, printed with a heavier cross than the operation
// A × B on sets of numbers: `A cross B`.
#let cross = math.class("binary", "⨯")
// An ordered n-tuple in the bold angle brackets of the book, `tuple(x_1, ...,
// x_n)`; the code ⟨x, y⟩ = τ(x, y) keeps the light ones, `chevron.l x, y
// chevron.r`.
#let tuple(..items) = math.lr(
  [#text(weight: "bold", sym.chevron.l)#(
      items
        .pos()
        .join(
          $,$,
        )
    )#text(weight: "bold", sym.chevron.r)],
)

// An upright insert in an italic statement.
#let roman(body) = text(style: "normal", body)

// A letterspaced word: a run-in head inside the text, the name of an author
// cited.
#let spaced(body) = text(
  tracking: 0.25em,
  spacing: 150%,
  ligatures: false,
  hyphenate: false,
  body,
)

// The author of a preface at the right.
#let signature(name) = block(above: 0.8em, width: 100%, align(
  right,
  name,
))

// «(a) … (b) …» and «(i) … (ii) …», as printed:
// `#enum(numbering: "(a)")[…][…]`, `#enum(numbering: "(i)")[…]`.
