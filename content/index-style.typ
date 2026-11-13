#import "main-defs.typ": *
#import "main-defs.typ" as defs
#import "numbering.typ": own-number

#let markup(term) = eval(term, mode: "markup", scope: dictionary(defs))

#let folio(location) = counter(page).at(location).first()
#let locator(location, shown: none) = box(context {
  metadata((
    kind: "cross-reference",
    target: "index-mark",
    resolved: true,
    target-location: location,
  ))
  link(location, if shown == none { str(folio(location)) } else { shown })
})

// The place a mark leads to: the mark itself, or the statement or heading
// named by its target.
#let mark-place(mark) = {
  let target = mark.value.at("target", default: none)
  if target == none { return mark.location() }
  let found = query(target)
  assert(found.len() == 1, message: "Index target must exist uniquely")
  found.first().location()
}

// The alphabetical index as the book prints it. Each mark gives a path; the
// elements of a path are the words the book replaces by one dash each, and an
// entry prints a dash for each element it shares with the entry before it:
// «Алгоритм, неформальное понятие (algorithm, informal notion) 17—22», «—
// нечисловой (non-numerical) 46—49». An element that begins with a comma
// joins the one before it without a space. After the entry: its English
// term in parentheses, its pages (a range from a pair of marks, «прим.» after
// a footnote), its cross-references «см.», «см. также».
#let join-path(parts) = {
  let shown = ""
  for part in parts {
    if shown == "" or part.starts-with(",") { shown += part } else {
      shown += " " + part
    }
  }
  shown
}
// Sorting: lower case without punctuation, element by element; ё as е. As in
// the book, the entries that begin with a Greek letter of a formula
// («μ-оператор», `$mu$-оператор`) follow the Cyrillic ones in the order of the
// Greek alphabet, and the Latin ones come last.
#let greek-letters = (
  alpha: "α",
  beta: "β",
  gamma: "γ",
  delta: "δ",
  epsilon: "ε",
  zeta: "ζ",
  eta: "η",
  theta: "θ",
  iota: "ι",
  kappa: "κ",
  lambda: "λ",
  mu: "μ",
  nu: "ν",
  xi: "ξ",
  omicron: "ο",
  pi: "π",
  rho: "ρ",
  sigma: "σ",
  tau: "τ",
  upsilon: "υ",
  phi: "φ",
  chi: "χ",
  psi: "ψ",
  omega: "ω",
)
#let sort-part(part) = {
  let key = lower(part)
  let names = regex("\\b(" + greek-letters.keys().join("|") + ")\\b")
  key = key.replace(regex("\\$[^$]*\\$"), formula => formula.text.replace(
    names,
    name => "\u{4fe}" + greek-letters.at(name.text),
  ))
  key = key.replace(regex("[,’'.$*()\\[\\]\"#^_]|super|sub"), "")
  key = key.replace("ё", "е").trim()
  key.replace(regex("[a-z]"), m => "\u{4ff}" + m.text)
}
#let sort-key(path) = path.map(sort-part).join("\u{1}")

#let index-entries = context {
  let entries = (:)
  let open = (:)
  for mark in query(<index-mark>) {
    let value = mark.value
    let path = value.path
    let key = sort-key(path)
    let record = entries.at(key, default: (
      path: path,
      en: none,
      places: (),
      see: none,
      see-also: none,
    ))
    if value.at("en", default: none) != none { record.en = value.en }
    for field in ("see", "see-also", "qualifier") {
      if value.at(field, default: none) != none {
        record.insert(field, value.at(field))
      }
    }
    let range = value.at("range", default: none)
    let place = mark-place(mark)
    if range == "start" {
      open.insert(key, open.at(key, default: ()) + (place,))
    } else if range == "end" {
      let starts = open.at(key, default: ())
      assert(
        starts.len() > 0,
        message: "Index range ends without a start: " + join-path(path),
      )
      record.places.push((
        start: starts.last(),
        end: place,
        note: value.at("note", default: false),
      ))
      open.insert(key, starts.slice(0, -1))
    } else if value.at("see", default: none) == none or range != none {
      record.places.push((
        start: place,
        end: none,
        note: value.at("note", default: false),
      ))
    }
    entries.insert(key, record)
  }
  // A range still open: an error in the final book; in a draft its other end
  // may be in a part not yet typeset, and the start page stands alone.
  let final = sys.inputs.at("stage", default: "final") == "final"
  for (key, starts) in open {
    assert(
      not final or starts.len() == 0,
      message: "Index range without an end: " + key,
    )
    for start in starts {
      let record = entries.at(key)
      record.places.push((start: start, end: none, note: false))
      entries.insert(key, record)
    }
  }
  let sorted = entries.values().sorted(key: entry => sort-key(entry.path))
  set par(first-line-indent: 0pt, justify: false, hanging-indent: 1.5em)
  set text(size: 8pt)
  let initial = none
  let previous = ()
  for entry in sorted {
    let path = entry.path
    let letter = sort-part(path.first()).clusters().first()
    if letter != initial {
      if initial != none { v(0.5em, weak: true) }
      initial = letter
      previous = ()
    }
    // The elements shared with the entry before it become dashes.
    let shared = 0
    while (
      shared < calc.min(path.len(), previous.len())
        and shared < path.len() - 1
        and sort-part(path.at(shared)) == sort-part(previous.at(shared))
    ) { shared += 1 }
    let rest = join-path(path.slice(shared)).trim(", ", at: start)
    // The first letter of an entry is a capital, but a Latin small letter
    // or a formula stays as it is, «m-сводимость».
    let initial = rest.clusters().first()
    let shown = if shared == 0 and initial.match(regex("[a-z$]")) == none {
      markup(upper(initial) + rest.slice(initial.len()))
    } else { markup(rest) }
    let dashes = range(shared).map(_ => [—~]).join()
    // The pages in order; a page inside a range of the same entry is not
    // repeated.
    let spans = entry.places.map(p => (
      first: folio(p.start),
      last: if p.end == none { folio(p.start) } else { folio(p.end) },
      place: p,
    ))
    let ranges = spans.filter(s => s.place.end != none)
    let kept = ()
    for s in spans.sorted(key: s => (s.first, -s.last)) {
      let inside = (
        s.place.end == none
          and ranges.any(r => (
            r.first <= s.first and s.first <= r.last
          ))
      )
      let repeated = kept.any(k => k.first == s.first and k.last == s.last)
      if not inside and not repeated { kept.push(s) }
    }
    let pages = kept
      .map(s => {
        let one = if s.first == s.last { locator(s.place.start) } else {
          locator(s.place.start) + [#sym.wj—#sym.wj] + locator(s.place.end)
        }
        if s.place.note [#one~прим.] else { one }
      })
      .join([, ])
    let english = if entry.en != none [ (#entry.en)]
    let qualifier = entry.at("qualifier", default: none)
    if qualifier != none { english = [#english (#qualifier)] }
    let see = if entry.see != none [ см. #markup(entry.see)]
    let also = if entry.see-also != none [; см. также #markup(entry.see-also)]
    block(width: 100%, above: 0pt, below: 0.5em, par[
      #dashes#shown#english#if pages != none [ #pages]#see#also
    ])
    previous = path
  }
}

// The index of notations: the signs in the order of the pages where they are
// introduced, each with its pages, in two columns, as printed.
#let notation-entries = context {
  let entries = (:)
  for mark in query(<notation-mark>) {
    let value = mark.value
    let key = if value.key != none { value.key } else { repr(value.sign) }
    let entry = entries.at(key, default: (
      sign: value.sign,
      places: (),
      order: value.at("order", default: none),
      sequence: entries.len(),
    ))
    let place = mark-place(mark)
    let range = value.at("range", default: none)
    if range == "end" {
      // The end of a range closes the place where it started.
      let last = entry.places.last()
      entry.places.at(-1) = (start: last.start, end: place)
    } else if entry.places.all(p => folio(p.start) != folio(place)) {
      entry.places.push((start: place, end: none))
    }
    entries.insert(key, entry)
  }
  let sorted = entries
    .values()
    .sorted(key: e => (
      folio(e.places.first().start),
      if e.order == none { 1000 + e.sequence } else { e.order },
    ))
  set par(first-line-indent: 0pt, justify: false)
  columns(2, gutter: 8mm, grid(
    columns: (1fr, auto),
    row-gutter: 0.55em,
    column-gutter: 1em,
    ..sorted
      .map(e => (
        e.sign,
        align(
          right,
          e
            .places
            .map(p => if p.end == none or folio(p.end) == folio(p.start) {
              locator(p.start)
            } else { locator(p.start) + [#sym.wj—#sym.wj] + locator(p.end) })
            .join([, ]),
        ),
      ))
      .flatten(),
  ))
}

// The index of theorems: for each chapter its theorems and their pages, from
// the theorems themselves.
#let theorem-entries = context {
  let rows = query(<numbered>)
    .filter(it => (
      type(it.value) == dictionary
        and it.value.at("family", default: none) == "th"
        and it.value.at("number", default: none) != none
    ))
    // A theorem printed in parts has one row, at its first part.
    .filter(it => {
      let printed = str(it.value.number.last())
      not printed.contains(" (") or printed.ends-with("(a)")
    })
    .map(it => {
      let chapter = counter(heading).at(it.location()).first()
      let own = counter("numbered:th").at(it.location()).first()
      (chapter: chapter, own: own-number("th", own), at: it.location())
    })
  // A theorem the book states again has one row with both pages, «XIV 254,
  // 258».
  let merged = ()
  for row in rows {
    if (
      merged.len() > 0
        and merged.last().chapter == row.chapter
        and merged.last().own == row.own
    ) {
      merged.last().places.push(row.at)
    } else {
      merged.push((chapter: row.chapter, own: row.own, places: (row.at,)))
    }
  }
  set par(first-line-indent: 0pt, justify: false)
  let cells = ()
  let current = none
  for row in merged {
    cells.push(if row.chapter != current { str(row.chapter) } else { [] })
    current = row.chapter
    cells.push(row.own)
    cells.push(row.places.map(place => locator(place)).join([, ]))
  }
  columns(2, gutter: 8mm, table(
    columns: (auto, auto, 1fr),
    align: (center, left, right),
    stroke: none,
    inset: (x: 0.3em, y: 0.18em),
    table.header([Глава], [Теорема], [Стр.]),
    ..cells,
  ))
}
