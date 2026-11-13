// Chapters 1–16 count on counter(heading), their sections § 1.1, § 1.2, … on
// its second level. In a chapter the theorems are numbered I, II, … in roman
// numerals, the exercises 1, 2, … in arabic ones, and so are the numbered
// lemmas and formulas; chapter() resets them. A corollary takes the number of
// the theorem before it, «Следствие VII».
//
// A reference prints the number as the book does: a theorem of the same
// chapter «VI», of another chapter «7-VI»; an exercise «14» or «7-14»; a
// section «7.4»; a chapter «7». The book itself sometimes writes the chapter
// in a reference inside the chapter; the source does not keep that.
#let statement-families = (
  "th",
  "cor",
  "lem",
  "prop",
  "def",
  "rem",
  "ex",
  "eq",
  "exm",
)
#let family-counter(family) = counter("numbered:" + family)
#let reset-numbering() = {
  for family in statement-families {
    family-counter(family).update(0)
  }
}

// The chapter of a location, 0 before chapter 1.
#let chapter-of(location) = {
  let numbers = counter(heading).at(location)
  if numbers.len() == 0 { 0 } else { numbers.first() }
}
#let place-key = chapter-of

// The own number of a statement: roman for the theorems and their corollaries.
#let own-number(family, value) = {
  let roman = family in ("th", "cor") and type(value) == int
  if not roman { value } else if value == 0 { "?" } else {
    numbering("I", value)
  }
}

// A primed formula «(3′)» shares the number of its base: the label of the
// primed formula is the label of the base with the ending -prime or -dprime,
// <eq:name> and <eq:name-prime>.
#let prime-suffixes = (prime: "′", dprime: "″")
#let formula-prime(name) = {
  let found = name.match(regex("^(.+)-(prime|dprime)$"))
  if found == none { return none }
  (
    base: label(found.captures.first()),
    mark: prime-suffixes.at(found.captures.last()),
  )
}

// (chapter, own number). A corollary counts nothing: it reads the theorem
// counter, or the number of the statement named by `base`. A lemma or a
// formula with a number given in the source keeps it (`fixed`).
#let object-number(
  family,
  location,
  suffix: none,
  prime: none,
  base: none,
  fixed: none,
) = {
  let source = if family == "cor" { "th" } else { family }
  let own = if fixed != none { fixed } else {
    own-number(family, family-counter(source).at(location).first())
  }
  if base != none {
    let found = query(selector(<numbered>).within(label(base)))
    own = if found.len() >= 1 { found.first().value.number.last() } else {
      "?"
    }
  }
  if suffix != none { own = str(own) + suffix }
  if prime != none {
    let base = query(selector(<numbered>).within(prime.base))
    own = if base.len() == 1 {
      str(base.first().value.number.last()) + prime.mark
    } else { "?" }
  }
  if family in ("bib", "fig") { (own,) } else { (chapter-of(location), own) }
}

// The number as printed at a place in chapter `here`: the own number, with
// the chapter of the target if that is another chapter.
#let printed-number(number, here) = {
  if number.len() == 1 { return str(number.first()) }
  let (chapter, own) = number
  if chapter == here or chapter == 0 { str(own) } else {
    str(chapter) + "-" + str(own)
  }
}

// The number of a record, counted at its place. The value that the record
// stores is right only from the second pass of the layout on, a reference that
// reads it from the third, and the book has no pass to spare.
#let record-number(record) = {
  let value = record.value
  let at = record.location()
  if "flags" in value {
    object-number(value.family, at, ..value.flags)
  } else if value.family == "heading" {
    counter(heading).at(at).slice(0, value.level)
  } else { value.number }
}
#let numbered-record(target) = {
  let found = query(target)
  if found.len() != 1 { return none }
  query(selector(<numbered>).within(target)).at(0, default: none)
}
#let record(family, ..flags) = context [#metadata((
  kind: "numbered",
  family: family,
  number: object-number(family, here(), ..flags.named()),
  flags: flags.named(),
))<numbered>]
