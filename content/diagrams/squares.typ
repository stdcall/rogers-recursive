// A commutative square of the book: four objects and four maps, the upper
// map labelled above, the lower one below, the vertical maps outside.
// `#comm-square($C$, $C$, $N$, $N$, $delta$, $gamma$, $gamma$, $phi$)`:
// the corners north-west, north-east, south-west, south-east, then the maps
// top, left, right, bottom. The coding square of § 1.8 and the square of
// theorem 4-II.
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

#let comm-square(
  nw,
  ne,
  sw,
  se,
  top,
  left-map,
  right-map,
  bottom,
  spacing: (26mm, 11mm),
) = {
  let corners = ((0, 0, nw), (1, 0, ne), (0, 1, sw), (1, 1, se))
  // From, to, label, the side of the label.
  let maps = (
    ((0, 0), (1, 0), top, left),
    ((0, 0), (0, 1), left-map, right),
    ((1, 0), (1, 1), right-map, left),
    ((0, 1), (1, 1), bottom, right),
  )
  block(width: 100%, above: 1em, below: 1em, align(center, diagram(
    spacing: spacing,
    label-sep: 3pt,
    ..corners.map(((x, y, name)) => node((x, y), name)),
    ..maps.map(((from, to, name, side)) => edge(
      from,
      to,
      "->",
      name,
      label-side: side,
    )),
  )))
}
