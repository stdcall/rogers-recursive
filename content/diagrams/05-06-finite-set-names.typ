// The three names of a finite set, § 5.6: a uniform passage goes along the
// arrows, from canonical indices to characteristic and to r. e. indices and
// from characteristic indices to r. e. indices, but not back.
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

// The names: place and text.
#let names = (
  ((0.5, 0), [Характеристические индексы]),
  ((0, 1), [Канонические индексы]),
  ((1, 1), [Р.~п. индексы]),
)
// The uniform passages: from, to.
#let passages = (
  ((0, 1), (0.5, 0)),
  ((0.5, 0), (1, 1)),
  ((0, 1), (1, 1)),
)

#let finite-set-names = block(width: 100%, above: 1em, below: 1em, align(
  center,
  diagram(
    spacing: (12mm, 8mm),
    node-inset: 2pt,
    // The arrows stop short of the names, clear of the descenders, as printed.
    node-outset: 3pt,
    ..names.map(((place, name)) => node(place, name)),
    ..passages.map(((from, to)) => edge(from, to, "->")),
  ),
))
