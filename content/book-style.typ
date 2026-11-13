#import "main-defs.typ": (
  petit-size, printed-title, reference-rules, spaced, without-notes,
)
#import "statements.typ": new-paragraph, numbered-display

// The page of the book, 60×90/16, 145×215 mm, with a type area 113.7 mm wide
// (25 ciceros) under the running head; the text is 10 pt on 10.8 pt, as
// printed.
#let page-width = 145mm
#let page-height = 215mm
#let body-margin = (left: 15.65mm, right: 15.65mm, top: 24mm, bottom: 25mm)
#let paragraph-indent = 1.5em
#let line-gap = 0.4em

// Capitals, a hyphen between letters not broken: «МНОГО-ОДНОСВОДИМОСТЬ».
#let upper-word(value) = upper(value).replace(
  regex("(\p{L})-(\p{L})"),
  m => m.captures.first() + "\u{2011}" + m.captures.last(),
)
// A title in capitals except its formulas.
#let upper-text(body) = {
  if type(body) == str { upper-word(body) } else if (
    body.func() == math.equation
  ) {
    body
  } else if body.func() == [].func() {
    // A short ending after a formula keeps its case, «КОДИРОВАНИЕ $n$-ок»; a
    // word after it does not, «$Pi_1^1$-МНОЖЕСТВА».
    let shown = ()
    let after-formula = false
    for child in body.children {
      let ending = if after-formula and child.func() == text {
        child.text.match(regex("^-\p{L}{1,3}\b"))
      }
      if ending != none {
        shown.push([#ending.text#upper(child.text.slice(ending.end))])
      } else { shown.push(upper-text(child)) }
      after-formula = child.func() == math.equation
    }
    shown.join()
  } else if body.func() == text { upper-word(body.text) } else if (
    body.func()
      in (
        emph,
        strong,
      )
  ) {
    body.func()(upper-text(body.body))
  } else { body }
}

// A title the book breaks into lines stands in one line in the contents.
#let one-line(body) = {
  if type(body) != content { body } else if (
    body.func() == linebreak
  ) [ ] else if (
    body.func() == [].func()
  ) { body.children.map(one-line).join() } else { body }
}

// A page that opens a chapter has neither running head nor folio.
#let opening-page() = {
  query(heading.where(level: 1))
    .map(it => it.location().page())
    .contains(here().page())
}

// The title in the running head: its short form if it has one.
#let running-title(it) = {
  if it.supplement in (auto, none) { it.body } else { it.supplement }
}

// The running head in small capitals over a rule, the folio outside: even
// pages «40 ГЛ. 1. РЕКУРСИВНЫЕ ФУНКЦИИ», odd pages «§ 1.1. НЕФОРМАЛЬНОЕ
// ПОНЯТИЕ АЛГОРИТМА 19», the last section begun on the page or before it. An
// unnumbered part (the prefaces, the introduction, the lists) gives its title
// on both.
#let running-header = context {
  if opening-page() { return }
  let chapters = query(heading.where(level: 1).before(here()))
  if chapters.len() == 0 { return }
  let chapter = chapters.last()
  let even = calc.even(counter(page).get().first())
  let middle = if chapter.numbering == none {
    upper-text(one-line(running-title(chapter)))
  } else if even {
    let number = counter(heading).at(chapter.location()).first()
    [ГЛ.~#number. #upper-text(running-title(chapter))]
  } else {
    let here-page = here().page()
    let sections = query(heading.where(level: 2).after(chapter.location()))
    let begun = sections.filter(it => (
      it.numbering != none and it.location().page() <= here-page
    ))
    if begun.len() == 0 {
      let number = counter(heading).at(chapter.location()).first()
      [ГЛ.~#number. #upper-text(running-title(chapter))]
    } else {
      let number = counter(heading).at(begun.last().location())
      [§~#number.map(str).join("."). #upper-text(running-title(begun.last()))]
    }
  }
  let folio = counter(page).display()
  set par(first-line-indent: 0pt, justify: false)
  set text(size: 7.5pt, tracking: 0.04em)
  block(
    width: 100%,
    stroke: (bottom: 0.4pt),
    inset: (bottom: 2pt),
    if even [#text(size: 10pt, tracking: 0pt, folio)#h(1.2em)#middle] else {
      align(right)[#middle#h(1.2em)#text(size: 10pt, tracking: 0pt, folio)]
    },
  )
}

// A formula in the line stands in text style; a line is opened up only as far
// as a tall formula needs, as in TeX: it may reach a little into the gap above
// and below, where the next line has its descenders and capitals. Only formulas
// with a tall construction are measured.
#let tall-marks = (
  "frac(",
  "binom(",
  "∑",
  "∏",
  "∫",
  "⋃",
  "⋂",
  "limits",
  "lr(",
  "mat(",
  "cases(",
  // A bar over a letter would touch the descenders of the line above.
  "overline(",
  // A superscript of a superscript, «$2^(2^(d + 1))$», stands as high.
  "t: attach(",
)
#let inline-equation-spaced(it) = {
  let source = repr(it.body)
  if tall-marks.any(mark => source.contains(mark)) {
    context {
      // The parts of the formula above and below the baseline. Text edges do
      // not cut a construction (limits, a bar, a big operator) at the
      // baseline, so each part is measured in a line beside a strut that
      // stands wholly above or wholly below the baseline.
      let strut = 100pt
      let part(shift) = (
        measure({
          set text(top-edge: "bounds", bottom-edge: "bounds")
          box(height: strut, baseline: shift)
          it
        }).height
          - strut
      )
      let below = part(0%)
      let above = part(100%)
      // The formula reaches into the space between the lines as far as the
      // text does: above the capital height no higher than a bracket, below
      // the baseline no lower than a descender. Two such lines keep the gap
      // of two lines of text. A bar over a letter stays out of the space: so
      // close under a descender it would read as underlining the line above.
      // Limits under an operator are as wide as a word and hang no lower
      // than a tenth of an em: the next line may have tall letters, «𝒜»,
      // right under them.
      let bar = if source.contains("overline(") { 0.067em } else { 0em }
      let hang = if source.contains("limits") { 0.1em } else { 0.25em }
      text(
        top-edge: calc.max(above + bar.to-absolute(), 0.75em.to-absolute())
          - 0.067em,
        bottom-edge: -calc.max(below, hang.to-absolute()) + hang,
        it,
      )
    }
  } else { it }
}
// A short formula stays whole in its line, «$n + 1$», «$1 <= k, 0 <= m$»: TeX
// discourages a break after a relation or an operation by a penalty, Typst
// breaks there as readily as between words.
#let short-formula = 6em
#let inline-equation-shown(it) = context {
  let shown = inline-equation-spaced(it)
  if measure(it).width < short-formula.to-absolute() { box(shown) } else {
    shown
  }
}
// A formula that opens with a closing delimiter stays on the line of the text
// before it: «… _сходится_$}$», «бесконечно$] => A$». Typst lays out the
// result of a show rule of a formula as one inline object, which a word
// joiner beside it does not bind to the word before: the leading delimiters
// are set as text of the math font, joined to the word, and the rest of the
// formula follows them as a formula. An empty ordinary atom before the rest
// keeps the spacing of an operator after the delimiter, «] ⇒ A».
// Whether a formula is inside `cases` (the rules of «если»).
#let inside-cases = state("inside-cases", false)
#let closing-delimiters = ("}", ")", "]")
#let opening-delimiters = ("{", "(", "[")
#let delimiter-text(parts) = text(
  font: "New Computer Modern Math",
  weight: "regular",
  style: "normal",
  parts.filter(part => part != [ ]).map(part => part.text).join(),
)
// Likewise a formula that ends with an opening delimiter stays with the word
// after it: «$<=> [$отношение …».
#let inline-equation(it) = {
  let parts = if it.body.func() == [].func() { it.body.children } else {
    (it.body,)
  }
  // A character of a formula is a `symbol` element.
  let count = 0
  for part in parts {
    if part.at("text", default: none) in closing-delimiters {
      count += 1
    } else if part == [ ] and count > 0 {
      count += 1
    } else { break }
  }
  let tail = 0
  for part in parts.slice(count).rev() {
    if part.at("text", default: none) in opening-delimiters {
      tail += 1
    } else if part == [ ] and tail > 0 {
      tail += 1
    } else { break }
  }
  if count == 0 and tail == 0 { return inline-equation-shown(it) }
  let middle = parts.slice(count, parts.len() - tail)
  let empty = math.class("normal", box(width: 0pt))
  if count > 0 {
    sym.wj
    delimiter-text(parts.slice(0, count))
  }
  if middle.len() > 0 {
    math.equation(block: false, [#if count > 0 { empty }#middle.join()#if (
        tail > 0
      ) { empty }])
  }
  if tail > 0 {
    delimiter-text(parts.slice(parts.len() - tail))
    sym.wj
  }
}


// Rules of the text and of formulas, shared by the book and the
// corrections sheet.
#let text-math-rules(body) = {
  // The blank line of the source opens a paragraph with its indent, also
  // after a display, a list or a heading; text without a blank line after a
  // display goes on with the sentence from the margin.
  show parbreak: it => {
    new-paragraph
    it
  }
  // «ℵ₀» typed as text (the English glosses of the index are strings) is the
  // formula, in the math font.
  show "ℵ₀": $aleph_0$
  // So is a class of a hierarchy written with Unicode indices, «Σ¹₂»,
  // «Π¹₁», «Δ¹₂».
  show regex("[ΣΠΔ][⁰¹²³⁴ⁿ][₀₁₂₃₄ₙ]"): it => {
    let digits = "0123456789n"
    let up = "⁰¹²³⁴⁵⁶⁷⁸⁹ⁿ".clusters()
    let down = "₀₁₂₃₄₅₆₇₈₉ₙ".clusters()
    let (base, top, bottom) = it.text.clusters()
    let name = (Σ: "Sigma", Π: "Pi", Δ: "Delta").at(base)
    let t = digits.clusters().at(up.position(c => c == top))
    let b = digits.clusters().at(down.position(c => c == bottom))
    eval("$" + name + "_" + b + "^" + t + "$")
  }
  // Abbreviations and initials stand with a thin space and do not break
  // inside: «т. е.», «А. Н. Колмогоров».
  show regex("\b\p{L}{1,2}\.(?:\u{a0}\p{L}{1,2}\.)+"): it => box(
    it.text.replace("\u{a0}", "\u{2009}"),
  )
  // A text hyphen following inline math belongs to the preceding symbol.
  show regex("-"): it => [#text("\u{2060}")#it]
  // A short ending stays with the formula before it: «$j$-м». Defined after
  // the rule for every hyphen, so that it applies first.
  show regex("-\p{Cyrillic}{1,3}\b"): it => [#sym.wj#box(it.text)]
  // A formula or a short Latin prefix before a hyphen is not left at the end
  // of a line: «$c$-эквивалентный», «tt-условие» stay whole.
  show regex("^-"): [#sym.wj#"-"#sym.wj]
  show regex("\b[A-Za-z]{1,3}-\p{Cyrillic}"): it => {
    let (prefix, rest) = it.text.split("-")
    [#prefix#sym.wj#"-"#sym.wj#rest]
  }
  // No line begins with a dash: «Гливенко—Кантелли», «$X$~— выборка».
  show "—": it => [#sym.wj#it]
  show "–": it => [#sym.wj#it]
  // Words inside formulas take the text face; the math font has no Cyrillic.
  // The regular weight of the math font: Typst would take its own Book weight
  // of New Computer Modern Math.
  show math.equation: set text(
    font: ("New Computer Modern Math", "New Computer Modern"),
    weight: "regular",
  )
  // A formula in bold text is bold too: the bold brackets of the book around
  // words, «*$chevron.l$*_состояние, …_*$chevron.r$*».
  show strong: it => {
    show math.equation: set text(weight: "bold")
    it
  }
  // As in TeX: delimiters keep their size around indices and fractions unless
  // a formula asks for growing ones, `grow((…))`.
  set math.lr(size: 1em)
  set math.cases(gap: 0.45em)
  show math.equation: it => {
    // The colon of "f: A -> B" is punctuation.
    show ":": math.class("punctuation", ":")
    // The indices of a relation stand at its side, «≤ₘ», «≡_T», «<^T», not
    // under or over it.
    show math.attach: a => {
      let base = a.base
      let char = if base.func() == text { base.text } else {
        base.at("text", default: none)
      }
      if (
        type(char) == str
          and char
            in (
              "≤",
              "≥",
              "<",
              ">",
              "=",
              "≡",
              "⊨",
              "⊢",
              "∼",
              "⩽",
              "⩾",
              "≰",
              "≱",
              "≢",
              "≮",
              "≯",
              "≠",
              "≈",
            )
          and (a.b != none or a.t != none)
      ) {
        math.attach(math.scripts(base), b: a.b, t: a.t)
      } else { a }
    }
    // «&», the conjunction of the book, is spaced as a relation.
    show "&": math.class("relation", sym.amp)
    // The word «если» of a formula has a word space before it also after a
    // comma and at the start of a column of `cases`, «1, если …», where Typst
    // gives a word in a formula a thin space or none.
    // An italic phrase of a formula, `#[_завершится (если …)_]`, keeps its own
    // spaces.
    show regex("^если$"): word => context if (
      text.style == "italic" or inside-cases.get()
    ) { word } else [#h(0.3em)#word]
    // The columns of `cases` stand a quad apart, as printed, «расходится   в
    // противном случае»; «если» at the start of a column takes no space of its
    // own there.
    show math.cases: it => {
      let gap = h(1em)
      let spaced(row) = {
        if row.func() != [].func() { return row }
        let parts = row.children
        let at = parts.position(part => repr(part.func()) == "align-point")
        if at == none or parts.at(at + 1, default: none) == gap { return row }
        (parts.slice(0, at + 1) + (gap,) + parts.slice(at + 1)).join()
      }
      let fields = it.fields()
      let children = fields.remove("children")
      let rows = children.map(spaced)
      inside-cases.update(true)
      if rows == children { it } else { math.cases(..fields, ..rows) }
      inside-cases.update(false)
    }
    // Russian words of a formula are set in the text face: the math font
    // has a few Cyrillic letters of its own (ш), upright in italic words.
    show regex("\p{Cyrillic}+"): word => text(
      font: "New Computer Modern",
      word,
    )
    // ≥ and ≤ are slanted, as printed.
    show "≥": sym.gt.eq.slant
    show "≤": sym.lt.eq.slant
    // Greek small letters are upright, as in the book: φ, ψ, λ, μ.
    show regex("[\u{03B1}-\u{03C9}\u{03D1}\u{03D5}\u{03F0}\u{03F1}\u{03F5}]"): (
      math.upright
    )
    it
  }
  show math.equation.where(block: false): inline-equation
  body
}

// The list of the sections of a chapter under its title: «§ 1.1. Неформальное
// понятие алгоритма 17», the page after the title.
#let chapter-sections(chapter) = context {
  let next = query(heading.where(level: 1).after(chapter.location())).filter(
    it => it.location() != chapter.location(),
  )
  let after = heading.where(level: 2).after(chapter.location())
  let sections = query(if next.len() == 0 { after } else {
    after.before(next.first().location())
  })
  set par(
    first-line-indent: 0pt,
    justify: false,
    leading: 0.3em,
    spacing: 0.3em,
  )
  set text(size: 8.5pt)
  pad(left: 18%, grid(
    columns: (auto, auto),
    column-gutter: 0.5em,
    row-gutter: 0.3em,
    ..sections
      .map(it => {
        let number = counter(heading).at(it.location()).map(str).join(".")
        let page = counter(page).at(it.location()).first()
        (
          link(it.location(), [§~#number.]),
          link(it.location(), [#one-line(without-notes(
              it.body,
            ))#sym.wj#box[#h(1.6em)#page]]),
        )
      })
      .flatten(),
  ))
}

// The plain text of a title, or none if it holds more than words.
#let title-text(body) = {
  if type(body) == str { body } else if body.has("text") { body.text } else if (
    body == [ ]
  ) { " " } else if body.func() == [].func() {
    let parts = body.children.map(title-text)
    if parts.all(part => part != none) { parts.join() }
  }
}
// «Глава 5. РЕКУРСИВНЫЕ И РЕКУРСИВНО / ПЕРЕЧИСЛИМЫЕ МНОЖЕСТВА»: a title too
// long for one line falls into two lines of nearly equal length under its
// first word, as printed; a closing «(часть 1)» stands on a line of its own
// in small letters. A title with a footnote is set as one paragraph.
#let chapter-title(label, body) = context {
  let printed = printed-title.get()
  let plain = if printed == none { title-text(body) }
  if plain == none {
    return [#label #upper-text(if printed == none { body } else { printed })]
  }
  let found = plain.match(regex("^(.*\S)\s+(\([^()]*\))$"))
  let (main, part) = if found == none { (plain, none) } else {
    (found.captures.first(), found.captures.last())
  }
  layout(size => {
    let room = size.width - measure[#label ].width
    let words = main.split(" ")
    let lines = (main,)
    if measure(upper-word(main)).width > room {
      let best = none
      for k in range(1, words.len()) {
        let first = words.slice(0, k).join(" ")
        let second = words.slice(k).join(" ")
        let widest = calc.max(
          measure(upper-word(first)).width,
          measure(upper-word(second)).width,
        )
        if best == none or widest < best.at(0) {
          best = (widest, (first, second))
        }
      }
      if best != none { lines = best.at(1) }
    }
    let shown = lines.map(upper-word)
    if part != none { shown.push(part) }
    grid(
      columns: (auto, 1fr),
      column-gutter: 0.3em,
      label,
      shown.join(
        linebreak(),
      ),
    )
  })
}

#let book-style(body) = {
  set page(
    width: page-width,
    height: page-height,
    margin: body-margin,
    numbering: "1",
    header: {
      counter(footnote).update(0)
      running-header
    },
    header-ascent: 4mm,
    footer: none,
  )
  set text(font: "New Computer Modern", size: 10pt, lang: "ru")
  set par(
    justify: true,
    leading: line-gap,
    spacing: line-gap,
    first-line-indent: paragraph-indent,
  )
  set heading(numbering: (..numbers) => {
    let n = numbers.pos()
    if n.len() == 1 { "Глава " + str(n.first()) + "." } else {
      "§ " + n.map(str).join(".") + "."
    }
  })
  // The footnotes of the book are marked «¹)», raised with their parenthesis,
  // on each page anew.
  set footnote(numbering: "1)")
  show footnote: set super(typographic: false)
  // A footnote mark stays on the line of the word before it, a narrow
  // no-break space after the word.
  show footnote: it => [#sym.wj#sym.space.nobreak.narrow#sym.wj#it]
  set footnote.entry(separator: line(length: 25%, stroke: 0.4pt))
  // Headings are set in the regular weight, as printed.
  show heading: set text(weight: "regular")
  show footnote.entry: it => {
    let note = it.note
    let mark = numbering(
      note.numbering,
      ..counter(footnote).at(note.location()),
    )
    set text(size: 8pt)
    set par(leading: 0.44em, first-line-indent: 1.5em)
    // The build compares the page of each entry with the page of its mark. A
    // note is not split across pages: Typst may begin a split note on the page
    // before the line of its mark (typst#5314).
    block(width: 100%, breakable: false)[#metadata((
        kind: "footnote-entry",
      ))#link(
        note.location(),
        super(typographic: false, mark),
      )#h(0.3em)#note.body]
  }
  // A chapter opens a page: «Глава 1. РЕКУРСИВНЫЕ ФУНКЦИИ» at its head, the
  // list of its sections under it. An unnumbered part: its title in capitals at
  // the head of the page, the text from some depth on.
  show heading.where(level: 1): it => {
    let numbered = it.numbering != none
    if numbered {
      context [#metadata((
        kind: "numbered",
        family: "heading",
        level: 1,
        number: (counter(heading).at(it.location()).first(),),
      ))<numbered>]
    }
    set par(first-line-indent: 0pt, justify: false)
    let title = context {
      // The title as printed, with its footnotes (main-defs.typ).
      let title = printed-title.get()
      if title == none { title = it.body }
      upper-text(title)
    }
    if numbered {
      block(width: 100%, above: 0pt, below: 0pt, {
        text(size: 14pt, chapter-title(
          [Глава #context counter(heading).at(it.location()).first().],
          it.body,
        ))
        v(9mm)
        chapter-sections(it)
        v(8mm)
      })
    } else {
      block(width: 100%, above: 0pt, below: 22mm, sticky: true, text(
        size: 14pt,
        title,
      ))
    }
  }
  // «§ 1.1. НЕФОРМАЛЬНОЕ ПОНЯТИЕ АЛГОРИТМА» in capitals at the margin.
  // A head inside a section, «Кодирования», «Формализация Тьюринга»: bold,
  // flush left, on a line of its own (subheading() of main-defs.typ).
  show heading.where(level: 3): it => block(
    width: 100%,
    above: 1.3em,
    below: 0.8em,
    sticky: true,
    par(first-line-indent: 0pt, justify: false, {
      // Its formulas are bold too, «Σ₀⁽ˢ⁾-классы».
      show math.equation: set text(weight: "bold")
      text(weight: "bold", it.body)
    }),
  )
  show heading.where(level: 2): it => {
    context [#metadata((
      kind: "numbered",
      family: "heading",
      level: 2,
      number: counter(heading).at(it.location()).slice(0, 2),
    ))<numbered>]
    set par(first-line-indent: 0pt, justify: false, leading: 0.35em)
    // A heading with a footnote is not sticky: when a sticky heading moves to
    // the next page, Typst leaves its footnote behind (typst#5314). It stands
    // in an unbreakable block with room for a few lines of text under it,
    // which goes to the next page whole, with its note, where the page has no
    // such room; the text after it is drawn up into that room.
    let room = 4.4em
    context {
      let title = printed-title.get()
      let noted = title != none and repr(title).contains("footnote")
      if title == none { title = it.body }
      let shown = block(
        width: 100%,
        above: 1.7em,
        below: 1em,
        sticky: not noted,
        text(size: 11pt, {
          let number = counter(heading).at(it.location()).map(str).join(".")
          [§~#number.#h(0.4em)]
          upper-text(title)
        }),
      )
      if noted {
        block(width: 100%, above: 1.7em, below: 0pt, breakable: false, {
          block(width: 100%, above: 0pt, below: 0pt, shown.body)
          v(room)
        })
        // Back up over the room; the weak space below the heading collapses
        // with that of the next paragraph or statement, as after a sticky one.
        v(-room)
        v(1em, weak: true)
      } else { shown }
    }
  }
  show: text-math-rules
  // Emphasis is italic type, not the toggle of emph: a reference number
  // inside it keeps its upright style.
  show emph: it => text(style: "italic", it.body)
  show math.equation.where(block: true): set block(above: 0.75em, below: 0.75em)
  // A display of many lines (a program of a machine) may break across pages;
  // one of up to four lines, and a numbered one, stays whole, the number «(E)»
  // at the left of its first line.
  show math.equation.where(block: true, numbering: none): it => {
    let rows = if it.body.func() == [].func() {
      it.body.children.filter(child => child.func() == linebreak).len() + 1
    } else { 1 }
    if rows > 4 {
      set block(breakable: true)
      it
    } else { it }
  }
  set math.equation(number-align: start + top)
  show math.equation.where(block: true): it => {
    let parts = if it.body.has("children") { it.body.children } else {
      (it.body,)
    }
    let done = parts.any(part => (
      part.func() == metadata
        and part.value.at("kind", default: none) == "book-display"
    ))
    if done or not (it.has("label") and str(it.label).starts-with("eq:")) {
      it
    } else { numbered-display(it) }
  }
  // Lists «(a) … (b) …» as printed: upright labels also inside italic
  // statements, the items indented.
  set enum(indent: 0pt, body-indent: 0.5em, numbering: (..n) => text(
    style: "normal",
    numbering("(a)", ..n),
  ))
  set list(indent: 1.5em)
  show figure: set block(above: 1.3em, below: 0.9em)
  show figure.caption: set text(size: 0.9em)
  show enum: it => if type(it.numbering) == str {
    let fields = it.fields()
    let children = fields.remove("children")
    let pattern = fields.remove("numbering")
    enum(
      ..fields,
      numbering: (..n) => text(style: "normal", numbering(pattern, ..n)),
      ..children,
    )
  } else { it }
  // A list of signs, `/ $cal(N)$: решетка …`: the signs ranged right in a
  // column at the paragraph indent, a dash, the descriptions hanging.
  show terms: it => context block(
    above: par.spacing,
    below: par.spacing,
    pad(left: paragraph-indent, grid(
      columns: (auto, auto, 1fr),
      column-gutter: 0.3em,
      row-gutter: par.leading,
      ..it
        .children
        .map(item => (align(right, item.term), [—], item.description))
        .flatten(),
    )),
  )
  show: reference-rules
  body
}

// The contents as printed: «Глава 1. РЕКУРСИВНЫЕ ФУНКЦИИ» with leaders and
// its page, the sections «§ 1.1. Неформальное понятие алгоритма» under it.
// Every entry links to its place.
#let contents-line(number, number-width, title, location) = {
  let page = counter(page).at(location).first()
  set par(first-line-indent: 0pt, justify: false)
  grid(
    columns: (number-width, 1fr, 2.2em),
    if number != none { link(location, number) },
    link(location, [#title#h(0.3em)#box(width: 1fr, repeat(gap: 0.45em)[.])]),
    align(right + bottom, link(location, str(page))),
  )
}
#let book-contents = context {
  let headings = query(heading).filter(it => it.outlined)
  set text(size: 9pt)
  for it in headings {
    let location = it.location()
    let numbers = counter(heading).at(location)
    if it.level == 1 and it.numbering == none {
      block(
        width: 100%,
        above: 0.35em,
        below: 0.35em,
        // The contents give an unnumbered part its short title, «Введение».
        contents-line(
          none,
          0pt,
          one-line(without-notes(running-title(it))),
          location,
        ),
      )
    } else if it.level == 1 {
      block(
        width: 100%,
        above: 0.9em,
        below: 0.35em,
        sticky: true,
        contents-line(
          none,
          0pt,
          [Глава #numbers.first(). #upper-text(one-line(without-notes(
              it.body,
            )))],
          location,
        ),
      )
    } else if it.level == 2 {
      block(width: 100%, above: 0.3em, below: 0.2em, pad(
        left: 1.5em,
        contents-line(
          [§~#numbers.slice(0, 2).map(str).join(".").],
          3.4em,
          one-line(without-notes(it.body)),
          location,
        ),
      ))
    }
  }
}
