// The diagrams of § 12.6: the implications between the almost-finiteness
// properties (1), (2), … of a set. A property is a node, an arrow an
// implication that holds; the book states that no other implications hold.
// The implications are given as chains, (1) ⇒ (2) ⇒ (3) …; each property
// stands at its column and row of the printed drawing; `pitch` is the distance
// between neighbouring columns and rows, measured on the printed drawing.
#import "@preview/fletcher:0.5.8" as fletcher: diagram, edge, node

// The lattice-theoretic properties (1)–(7): from (2) one chain through the
// cohesive-like properties (3), (4) and one through the indecomposable ones
// (5), (6), both ending in immunity (7).
#let lattice-theoretic-implications = (
  places: (
    "1": (0, 1),
    "2": (1, 1),
    "3": (2, 0),
    "4": (3, 0),
    "5": (2, 2),
    "6": (3, 2),
    "7": (4, 1),
  ),
  chains: (("1", "2", "3", "4", "7"), ("2", "5", "6", "7")),
  pitch: (12.3mm, 9.3mm),
)

// With the recursively invariant properties (8)–(10): the upper chain passes
// through (8), (9), (10) to (7); (6) implies (10) as well.
#let recursively-invariant-implications = (
  places: (
    "1": (0, 1),
    "2": (1, 1),
    "3": (2, 0),
    "4": (3, 0),
    "8": (4, 0),
    "9": (5, 0),
    "10": (6, 0),
    "7": (7, 1),
    "5": (3, 2),
    "6": (5, 2),
  ),
  chains: (
    ("1", "2", "3", "4", "8", "9", "10", "7"),
    ("2", "5", "6", "7"),
    ("6", "10"),
  ),
  pitch: (10.3mm, 7mm),
)

// The drawing of a set of implications, centred, its labels «(n)» in the
// small bold type of the book's drawings, the arrows close to them.
#let implications(data) = {
  // Every link of a chain is an arrow; each property of a chain has a place.
  let arrows = data.chains.map(chain => chain.windows(2)).join()
  for (from, to) in arrows {
    assert(from in data.places and to in data.places)
  }
  let label(name) = text(
    size: 8pt,
    weight: "bold",
    top-edge: "bounds",
    bottom-edge: "bounds",
  )[(#name)]
  block(width: 100%, above: 1.2em, below: 1.2em, align(center, diagram(
    cell-size: data.pitch,
    spacing: 0pt,
    mark-scale: 130%,
    node-inset: 0.8pt,
    edge-stroke: 0.45pt,
    ..data.places.pairs().map(((name, place)) => node(place, label(name))),
    ..arrows.map(((from, to)) => edge(
      data.places.at(from),
      data.places.at(to),
      "-stealth",
    )),
  )))
}
