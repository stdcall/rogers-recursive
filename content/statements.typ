#import "numbering.typ": family-counter, formula-prime, own-number, record
#import "main-defs.typ": new-paragraph, petit, spaced
#let sequence = [].func()
#let join-pieces(pieces) = sequence(
  pieces
    .map(it => if it.func() == sequence and not it.has("label") {
      it.children
    } else { (it,) })
    .flatten(),
)
#let keep-label(original, rebuilt) = {
  if original.has("label") [#rebuilt#original.label] else { rebuilt }
}

// A statement that opens with a list keeps its first item on the line of the
// head, as printed, «ТЕОРЕМА II. (a) … », the other items below it: the first
// item becomes the opening paragraph and the list goes on from (b).
#let lift-first-item(body) = {
  let parts = if body.func() == sequence { body.children } else { (body,) }
  let skip = (it => it.func() in ([ ].func(), parbreak))
  let first = parts.position(it => not skip(it))
  if first == none { return body }
  let lead = parts.at(first)
  let (pattern, items, after, fields) = if lead.func() == enum.item {
    let end = first
    while (
      end < parts.len()
        and (parts.at(end).func() == enum.item or skip(parts.at(end)))
    ) { end += 1 }
    (
      auto,
      parts.slice(first, end).filter(it => it.func() == enum.item),
      parts.slice(end),
      (:),
    )
  } else if lead.func() == enum {
    let fields = lead.fields()
    let children = fields.remove("children")
    (
      fields.at("numbering", default: auto),
      children,
      parts.slice(first + 1),
      (
        fields
      ),
    )
  } else { return body }
  if items.len() == 0 { return body }
  let start = fields.at("start", default: 1)
  let label = context {
    let shown = if pattern == auto { enum.numbering } else { pattern }
    if type(shown) == str {
      text(style: "normal", numbering(shown, start))
    } else { numbering(shown, start) }
  }
  let rest = items.slice(1).map(it => it.body)
  let list = if rest.len() > 0 {
    let options = fields
    let _ = options.remove("start", default: none)
    enum(..options, start: start + 1, ..rest)
  }
  join-pieces((
    ..parts.slice(0, first),
    [#label #items.first().body],
    ..if list != none { (list,) } else { () },
    ..after,
  ))
}

// Put `head` at the start of the first paragraph of `body`.
#let prepend-heading(body, head) = {
  if (
    body.func() in (table, grid, figure, list, enum, terms)
      or (
        body.func() == math.equation and body.block
      )
  ) {
    // The head stays with the formula, table or list that follows it; the
    // empty paragraph before it gives it the indent of the other heads.
    let shown-head = block(sticky: true, context {
      par(spacing: 0pt)[]
      v(-par.spacing)
      par(head)
    })
    shown-head + body
  } else if body.func() == block {
    let fields = body.fields()
    let inner = fields.remove("body")
    block(prepend-heading(inner, head), ..fields)
  } else if body.func() == sequence and body.children.len() > 0 {
    let children = body.children
    let first = children.position(it => (
      it.func()
        not in (
          [ ].func(),
          parbreak,
        )
    ))
    if first == none { join-pieces((head, body)) } else {
      keep-label(body, join-pieces((
        ..children.slice(0, first),
        prepend-heading(children.at(first), head),
        ..children.slice(first + 1),
      )))
    }
  } else { head + body }
}

// Put `ending` after the last word or formula of `body`.
#let append-ending(body, ending) = {
  if body.func() == math.equation and body.block {
    // The mark follows the last line of a display, as printed.
    keep-label(body, math.equation(
      block: true,
      $#body.body quad square.filled.small$,
    ))
  } else if body.func() in (block, box) {
    let fields = body.fields()
    let inner = fields.remove("body")
    body.func()(append-ending(inner, ending), ..fields)
  } else if body.func() == sequence and body.children.len() > 0 {
    let children = body.children
    let last = children
      .rev()
      .position(it => it.func() not in ([ ].func(), parbreak))
    if last == none { join-pieces((body, ending)) } else {
      let index = children.len() - last - 1
      keep-label(body, join-pieces((
        ..children.slice(0, index),
        append-ending(children.at(index), ending),
        ..children.slice(index + 1),
      )))
    }
  } else { body + ending }
}

// The end of a proof, «■», close after the last word.
#let qed-mark = [#sym.wj#h(0.15em)#sym.wj#box($square.filled.small$)]

// A statement and a proof stand apart from the text with a little space
// above and below them, as printed; the space is weak and collapses with
// that of a neighbour.
#let statement-space = 0.55em

// A statement, a proof or an exercise opens a block of its own: it ends the
// paragraph before it whether or not the source has a blank line there.
// Inside, the empty paragraph gives the first line its indent. The text after
// it without a blank line goes on from the margin, as after a display.
//
// A statement with a footnote or an editorial note stays in the flow of the
// page instead: there a line with a note mark goes to the next page together
// with its note, while a block keeps the line and sends the note on. Empty
// blocks keep the space above and below.
#let statement-block(body, space: statement-space, after: auto) = context {
  let after = if after == auto { space } else { after }
  let opening = {
    par(spacing: 0pt)[]
    v(-par.spacing)
    body
  }
  let source = repr(body)
  if source.contains("footnote") or source.contains("editorial-note") {
    block(width: 100%, above: par.spacing + space, below: 0pt)
    opening
    block(width: 100%, above: par.spacing + after, below: 0pt)
  } else {
    block(
      width: 100%,
      breakable: true,
      above: par.spacing + space,
      below: par.spacing + after,
      opening,
    )
  }
}

// An italic statement: also the words inside its formulas («где», «и») are
// italic, as printed; they take the text face. Numbers and references stay
// upright.
#let italic-body(body) = {
  show math.equation: it => {
    show regex("\p{Cyrillic}+"): t => context if text.style == "italic" {
      text(font: "New Computer Modern", style: "italic", t)
    } else { t }
    it
  }
  show regex("§|\b(?:\d+|[IVXL]+)\b\)?"): it => text(style: "normal", it)
  text(style: "italic", body)
}

// The head of a statement in small capitals, «ТЕОРЕМА VII.», «ОПРЕДЕЛЕНИЕ.».
#let statement-word(word) = text(style: "normal", smallcaps(word))

// «ТЕОРЕМА VII.» and the statement in italic. `numbered: false` for an
// unnumbered statement («ЛЕММА.», «ОПРЕДЕЛЕНИЕ.»); `number:` a number given
// by the book, «ЛЕММА 2.»; `title`: a name in parentheses after the number;
// `word`: the head in place of the kind; `suffix`: a variant that shares the
// number of the statement before it, «Следствие XII (a)»; `base`: the label
// of the statement whose number it carries, where others stand between them;
// `step: true` with `suffix` for the first part of a theorem printed in parts,
// «ТЕОРЕМА III (a).», the next parts with `suffix` alone.
#let statement(
  kind,
  family,
  body,
  numbered: true,
  number: none,
  title: none,
  word: none,
  italic: true,
  suffix: none,
  base: none,
  counts: true,
  step: auto,
) = {
  let steps = if step == auto {
    numbered and counts and suffix == none and number == none and base == none
  } else { step }
  if steps { family-counter(family).step() }
  let head = {
    if numbered {
      record(family, suffix: suffix, base: base, fixed: number)
    } else {
      [#metadata((kind: "numbered", family: family, number: none))<numbered>]
    }
    statement-word(if word == none { kind } else { word })
    if numbered {
      [ ]
      context {
        let source = if family == "cor" { "th" } else { family }
        let own = if number != none { number } else if base == none {
          own-number(family, family-counter(source).get().first())
        } else {
          let found = query(selector(<numbered>).within(label(base)))
          if found.len() >= 1 { found.first().value.number.last() } else { "?" }
        }
        text(style: "normal")[#own#suffix]
      }
    }
    if title != none {
      [ ]
      text(style: "normal")[(#title)]
    }
    text(style: "normal")[.]
    [ ]
  }
  body = lift-first-item(body)
  if italic { body = italic-body(body) }
  statement-block(prepend-heading(body, head))
}
#let theorem(body, ..args) = statement("Теорема", "th", body, ..args)
// A corollary carries the number of the theorem before it; a second
// corollary of the same theorem names its letter, `suffix: " (b)"`.
#let corollary(body, ..args) = statement("Следствие", "cor", body, ..args)
#let lemma(body, numbered: false, ..args) = statement(
  "Лемма",
  "lem",
  body,
  numbered: numbered,
  ..args,
)
#let definition(body, ..args) = statement(
  "Определение",
  "def",
  body,
  numbered: false,
  italic: false,
  ..args,
)
// «ЗАМЕЧАНИЕ.»; the numbered remarks of a chapter, «ЗАМЕЧАНИЕ 1.», are
// `#remark(numbered: true)[…] <rem:name>`.
#let remark(body, numbered: false, ..args) = statement(
  "Замечание",
  "rem",
  body,
  numbered: numbered,
  italic: false,
  ..args,
)
// «ПРЕДЛОЖЕНИЕ 1.», numbered in the chapter, its text upright.
#let proposition(body, ..args) = statement(
  "Предложение",
  "prop",
  body,
  italic: false,
  ..args,
)

// A numbered example of a section, «П р и м е р 2.» letterspaced and its
// text upright: `#example[…] <exm:name>`; the numbers restart in each
// section, `@exm:name` prints «2»; `restart: true` begins a new series of
// examples inside a section, «Пример 1» again.
#let example(body, restart: false) = {
  if restart { family-counter("exm").update(0) }
  family-counter("exm").step()
  let head = {
    record("exm")
    context [#spaced[Пример] #family-counter("exm").get().first(). ]
  }
  statement-block(prepend-heading(body, head), space: 0pt)
}

// A named point of the text, a paragraph that opens with its symbol: `#point(
// "*1")[_Алгоритм задается …_ (Любой …)] <ax:name>`; `@ax:name` prints «*1».
#let point(symbol, body) = {
  let head = [#metadata((
      kind: "numbered",
      family: "ax",
      number: (symbol,),
      symbol: symbol,
    ))<numbered>#text(style: "normal", symbol + ".")
  ]
  statement-block(prepend-heading(body, head), space: 0pt)
}

// A run-in head in letterspaced type, «П р и м е р ы.», «Э т а п 1.»,
// «Ф о р м а л ь н о е  и з л о ж е н и е.»: the word and its period, then the
// text of the paragraph.
#let run-in(word) = {
  // A number or a letter in parentheses is not letterspaced: «Э т а п 1.»,
  // «П о д э т а п (a).».
  show regex("[0-9]+|\(\w\)"): it => text(tracking: 0pt, it)
  [#spaced(word). ]
}

// «Д о к а з а т е л ь с т в о.» and the proof, closed by «■». `of` names what
// is proved: `#proof(of: [теоремы~@th:name])[…]` gives «Доказательство
// теоремы V.»; `head` replaces the word, «Более формальное доказательство»;
// `head: none` for a proof the book opens without a head; `qed: false` where
// the book prints no end mark.
//
// A proof without a head either opens with the word in its sentence,
// «#spaced[Доказательство] очевидно.», and stands apart like any proof, or
// goes on with the proof of a theorem after a lemma and its proof: then its
// text runs on as paragraphs of that proof, as printed.
#let opens-with-head(body) = {
  let parts = if body.func() == sequence { body.children } else { (body,) }
  let first = parts.find(it => (
    it.func() not in ([ ].func(), parbreak, metadata)
  ))
  // `spaced` gives a styled piece of text, «styled(child: [Доказательство])».
  first != none and repr(first).starts-with("styled(child: [Доказательство")
}
#let proof(body, of: none, head: [Доказательство], qed: true) = {
  if qed { body = append-ending(body, qed-mark) }
  if head == none and not opens-with-head(body) {
    return body
  }
  // «Д о к а з а т е л ь с т в о  с л е д с т в и я.»: the whole head
  // letterspaced, a number in it not.
  let start = if head == none { [] } else {
    // The space between the head and `of` is letterspaced too.
    spaced(if of == none { head } else [#head #of])
    [. ]
  }
  // A proof without the end mark goes on in the text after it: no space
  // below.
  statement-block(prepend-heading(body, start), after: if qed {
    statement-space
  } else { 0pt })
}

// An exercise of the closing section «Упражнения» of a chapter, numbered
// through the chapter, «2-1.», in small type: `mark: "open"` puts «△» before
// the number of a harder exercise, `mark: "solid"` «▲» before one of the
// hardest; `@ex:name` prints «1» in the chapter and «2-1» outside it.
#let triangle-marks = (
  open: $triangle.stroked.t$,
  solid: $triangle.filled.t$,
)
// `period: false` where the book prints the number without a period, «4-1
// (a) …».
#let exercise(body, mark: none, period: true) = {
  family-counter("ex").step()
  let head = {
    record("ex")
    if mark != none {
      // The mark hangs before the number, in the indent.
      box(width: 0pt, align(right, box(
        triangle-marks.at(mark) + h(0.15em),
      )))
    }
    context {
      let chapter = counter(heading).get().first()
      strong[#chapter\-#family-counter("ex").get().first()#if period [.]]
      [ ]
    }
  }
  petit(statement-block(prepend-heading(body, head), space: 0pt))
}

// The mark of a harder part of an exercise, before its letter, «△(d)»: a part
// set as a paragraph that begins `#exercise-mark("open")(d) …`.
#let exercise-mark(mark) = [#triangle-marks.at(mark)#h(0.1em)]

// The heading of a group of exercises, «§ 1.1—1.10», centred.
#let exercise-group(body) = block(
  width: 100%,
  above: 1.1em,
  below: 0.7em,
  sticky: true,
  align(center, text(size: 9pt, weight: "bold", body)),
)

// A display with a label <eq:…> takes its number, with the text after it in
// the upright of the text also inside an italic statement.
#let numbered-display(it) = {
  let prime = formula-prime(str(it.label))
  math.equation(
    block: true,
    numbering: _ => context {
      let own = if prime == none {
        str(family-counter("eq").get().first())
      } else {
        let base = query(selector(<numbered>).within(prime.base))
        if base.len() == 1 {
          str(base.first().value.number.last()) + prime.mark
        } else { "?" }
      }
      text(style: "normal")[(#own)]
    },
    [#metadata((kind: "book-display"))#if prime == none {
        family-counter("eq").step()
      }#record("eq", prime: prime)#it.body],
  )
}

// A display with a symbolic number, «(∗)», «(D₁)»: a string or a formula;
// `@eq:…` prints the same.
#let symbolic-display(symbol, body) = math.equation(
  block: true,
  numbering: _ => text(style: "normal")[(#symbol)],
  [#metadata((kind: "book-display"))#metadata((
      kind: "numbered",
      family: "eq",
      number: ("symbol",),
      symbol: symbol,
    ))<numbered>#body.body],
)
