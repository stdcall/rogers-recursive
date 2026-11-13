// The book's bibliography: works grouped by author, "А д д и с о н
// (A d d i s o n J. W.)", each under its year, "[1955]", "[1959a]". A
// reference in the text names the author in words and cites the work:
// `Пост~@bib:Post1944` prints "Пост [1944]". Every description is generated
// from references.bib (or editorial.bib); this file only orders the records.
#import "bibliography-data.typ": bibliography-data, name-parts
#import "numbering.typ": family-counter, record
#import "main-defs.typ": reference-rules

// `annotation` is the printed description with substitutions: {title},
// {pages}, … from this record, {Key.pages} from a related component;
// `_{booktitle}_` sets a value in italics. `_…_` in a value is emphasis,
// `$…$` mathematics.
#let rich-bib-text(value) = {
  // An abbreviation stays with the number or word after it: «vol. 8».
  let value = value
    .replace("'", "’")
    .replace("--", "–")
    .replace("~", "\u{00a0}")
    .replace(
      regex("\\b(vol|Vol|Bd|ser|Ser|No|Nr|ed|т|вып|гл|ч|изд|p|pp|S|стр)\\. "),
      m => m.text.slice(0, -1) + "\u{00a0}",
    )
  let position = 0
  for match in value.matches(regex("_[^_]+_|\\$[^$]+\\$")) {
    value.slice(position, match.start)
    let part = match.text
    if part.starts-with("_") {
      emph(part.slice(1, -1))
    } else { eval(part, mode: "markup") }
    position = match.end
  }
  value.slice(position)
}

// Names as the book prints them: the Russian surname spaced out, then the
// initials, "А д я н С. И."; an original name in parentheses after it as
// written, "(Ackermann W.)"; "Jr." after a comma, "Hall M., Jr.", or, in a
// list of several names, after a space.
#let spaced(body) = text(
  tracking: 0.25em,
  spacing: 150%,
  ligatures: false,
  hyphenate: false,
  body,
)
// The initials do not break; initials written before the surname, «Ю.
// Робинсон», stay unspaced in front of it.
#let print-name(name, plain: false) = {
  let parts = name-parts(name)
  let family = parts.family
  let prefix = family.match(regex("^((?:\\p{Lu}\\.\\s*)+)(\\S.*)$"))
  let initials = none
  if prefix != none {
    initials = prefix.captures.first().trim().replace(" ", "\u{00a0}")
    family = prefix.captures.last()
  }
  let shown = if plain { family } else { spaced(family) }
  if initials != none { shown = [#initials\u{00a0}#shown] }
  if parts.given != none {
    shown = [#shown\u{00a0}#parts.given.replace(" ", "\u{00a0}")]
  }
  if parts.suffix != none { shown = [#shown, #parts.suffix] }
  shown
}
// Several names are joined by commas; `conjunction: true` puts «и» before
// the last one, as the Russian names of a group heading print.
#let print-names(value, plain: false, conjunction: false) = {
  let shown = value.split(" and ").map(name => print-name(name, plain: plain))
  if shown.len() > 1 and conjunction {
    shown.slice(0, -1).join(", ") + [#h(0.6em)и#h(0.6em)] + shown.last()
  } else { shown.join(", ") }
}

// Group headings and entries follow each other at the leading of the text,
// as printed.
#let entry-spacing = 0.52em

// Page list of the mentions of a work, each linked to its mention.
#let bib-backlinks(target) = context {
  let refs = query(<bibliography-mention>).filter(it => {
    let value = it.value
    (
      type(value) == dictionary
        and value.at("target", default: none) == target
        and value.at("bibliographic-mention", default: true)
    )
  })
  let seen = ()
  let pages = ()
  for mention in refs.sorted(key: it => it.location().page()) {
    let loc = mention.location()
    if not seen.contains(loc.page()) {
      seen.push(loc.page())
      let position = loc.position()
      let destination = (
        page: position.page,
        x: position.x,
        y: calc.max(0pt, position.y - 8pt),
      )
      let shown = str(counter(page).at(loc).first())
      pages.push(box(context [
        #metadata((
          kind: "page-reference",
          resolved: true,
          target: "bib-mention:" + target,
          position: here().position(),
          target-position: position,
          // Typst adds 10pt above the coordinate destination as well.
          destination-offset-pt: 18,
          description: shown,
        ))
        #link(destination, shown)
      ]))
    }
  }
  if pages.len() > 0 [ #text(size: 7.5pt)[\[с.~#pages.join(", ")\]]]
}

// The printed description of a record from its annotation template. The
// journal is printed as the book abbreviates it, `shortjournal` when there is
// one, and the volume of a journal in bold, as in the book; {author} prints
// the names as in a group heading.
#let bib-description(key) = {
  let entry = bibliography-data.at(key)
  let related = entry
    .at("related", default: "")
    .split(",")
    .map(k => k.trim())
    .filter(k => k != "")
  let template = entry.annotation
  let position = 0
  for match in template.matches(regex("([_*]?)\\{([^{}]+)\\}([_*]?)")) {
    rich-bib-text(template.slice(position, match.start))
    let (before, name, after) = match.captures
    position = match.end
    // {spaced:Ван Хао}: a name letterspaced as printed; {cite:Key}: a
    // reference to another work of the list, not a mention of it.
    if name.starts-with("spaced:") {
      [#before#spaced(name.slice(7))#after]
      continue
    }
    if name.starts-with("cite:") {
      [#before#reference-rules(
          ref(label("bib:" + name.slice(5))),
          bibliographic-mention: false,
        )#after]
      continue
    }
    let token = name.split(".")
    let data = if token.len() == 1 { entry } else {
      assert(
        token.first() in related,
        message: "Template references an unrelated bibliography record",
      )
      bibliography-data.at(token.first())
    }
    let field = token.last()
    assert(field in data, message: "No field " + name + " for " + key)
    let value = if field == "journal" {
      rich-bib-text(data.at("shortjournal", default: data.journal))
    } else if field == "author" {
      print-names(data.author)
    } else if field == "volume" and "journal" in data {
      strong(rich-bib-text(data.volume))
    } else {
      rich-bib-text(data.at(field))
    }
    if before == "_" and after == "_" { emph(value) } else if (
      before == "*" and after == "*"
    ) { strong(value) } else [#before#value#after]
  }
  rich-bib-text(template.slice(position))
  // A composite record (a paper and its correction) lists its DOIs in turn.
  let dois = (key, ..related)
    .map(component => bibliography-data.at(component).at("doi", default: none))
    .filter(doi => doi != none)
  // A line may end after the first slash and, in the suffix, after a hyphen,
  // a point or a slash («S0002-9947-1959-…» would not break otherwise; before a
  // hyphen the word joiner of the hyphen rule forbids a break). A break point
  // is a vanishing space: it adds no character to the text of the DOI (a
  // zero-width space would), and `h(0pt)` gives no break point.
  let break-point = h(0.001pt)
  let shown(doi) = {
    let (prefix, ..rest) = doi.split("/")
    let pieces = ("",)
    for character in rest.join("/").clusters() {
      pieces.at(-1) += character
      if character in ("-", ".", "/") { pieces.push("") }
    }
    [DOI: #prefix/#break-point#pieces.join(break-point)]
  }
  if dois.len() > 0 {
    [ ]
    dois.map(doi => link("https://doi.org/" + doi, shown(doi))).join("; ")
  }
}

// The heading of an author's group, from its first record: the Russian
// form of the names, `authorru`, spaced, then the original names in
// parentheses, spaced too, "А д д и с о н (A d d i s o n J. W.)". A Russian
// author prints the name only, "А р с л а н о в М. М.".
#let bib-years = state("bib-years", (:))
#let bib-group(key) = {
  let entry = bibliography-data.at(key)
  // Russian co-authors are joined by «и», as printed.
  let shown = if "authorru" in entry [#print-names(entry.authorru)
    (#print-names(entry.author))] else {
    print-names(entry.author, conjunction: true)
  }
  bib-years.update((:))
  block(above: 1.1em, below: 0.45em, sticky: true, width: 100%, par(
    first-line-indent: 0pt,
    hanging-indent: 1.2em,
    justify: false,
    shown,
  ))
}

// The editor's text that opens a list: its references to the list itself
// are not mentions of the works.
#let bib-preface(body) = reference-rules(body, bibliographic-mention: false)

// A work of the current group: `#bib-item("Addison1959a") <bib:Addison1959a>`.
// Its label is the year of the record, with a letter after the first work of
// the same year in the group, "[1959]", "[1959a]"; `label` gives a label the
// book prints otherwise. A work added in the translation (`keywords =
// {translation}` in references.bib) has a star after its label, "[1968]*". A
// reference prints the label, "[1959a]".
#let bib-letters = "abcdefghijklmnopqrstuvwxyz".clusters()
#let bib-item(key, label: none) = {
  let entry = bibliography-data.at(key)
  let year = entry.year
  bib-years.update(years => {
    years.insert(year, years.at(year, default: 0) + 1)
    years
  })
  let star = "translation" in entry.at("keywords", default: "")
  // Words in Latin letters hyphenate by the language of the work; a Russian
  // note in the same description keeps the Russian rules.
  let lang = (english: "en", french: "fr", german: "de").at(
    entry.at("language", default: "english"),
    default: "en",
  )
  show regex("\p{Latin}[\p{Latin}'’]*"): set text(lang: lang)
  block(spacing: entry-spacing, width: 100%, context {
    let count = bib-years.get().at(year)
    let shown = if label != none { label } else if count == 1 { year } else {
      year + bib-letters.at(count - 2)
    }
    pad(left: 1.2em, grid(
      columns: (4.2em, 1fr),
      [#record("bib", fixed: shown)\[#shown\]#if star [\*]],
      par(first-line-indent: 0pt)[#bib-description(key)#bib-backlinks(
          "bib:" + key,
        )],
    ))
  })
}
