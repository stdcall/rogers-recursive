// The binary trees of § 9.9 (exercises 9-40 and 9-44). A vertex is the
// sequence of turns leading to it from the root, «1» up and «0» down; the
// tree grows to the right. A drawn vertex whose child is not drawn goes on
// to that child as a branch ending in dots.
#import "@preview/cetz:0.5.2": canvas, draw

// Exercise 9-40: the vertices are labelled by their sequences.
#let sequence-tree = (
  vertices: ("", "1", "0", "11", "10"),
  label: turns => if turns == "" { $emptyset$ } else { turns },
)

// Exercise 9-44 (iv): the vertices are numbered level by level from the root
// 0, the children of n being 2n + 1 (up) and 2n + 2 (down).
#let numbered-tree = (
  vertices: ("", "1", "0", "11", "10", "01", "00"),
  label: turns => str(turns
    .clusters()
    .fold(0, (n, turn) => (
      2 * n + if turn == "1" { 1 } else { 2 }
    ))),
)

// Lengths in millimetres, from the printed drawings: the distance between
// the ends of neighbouring branches, the step between levels, the dots that
// end a branch and the gap before them.
#let branch-gap = 5.3
#let level-step = 15.5
#let dot-count = 5
#let dot-step = 2.3
#let dot-gap = 1.6

#let binary-tree(tree) = align(center, block(
  above: 1.6em,
  below: 1.4em,
  canvas(length: 1mm, {
    import draw: *
    // The ends of the branches are the children of the deepest vertices.
    let depth = calc.max(..tree.vertices.map(turns => turns.len())) + 1
    // A vertex of length k has its children 2^(depth - k - 2) gaps above and
    // below it.
    let place(turns) = (
      turns.len() * level-step,
      turns
        .clusters()
        .enumerate()
        .map(((k, turn)) => (
          (if turn == "1" { 1 } else { -1 })
            * branch-gap
            * calc.pow(2, depth - k - 2)
        ))
        .sum(default: 0),
    )
    let name(turns) = "v" + turns
    for turns in tree.vertices {
      content(
        place(turns),
        text(size: 8pt, weight: "bold", (tree.label)(turns)),
        name: name(turns),
        padding: 0.6,
      )
    }
    for turns in tree.vertices {
      for child in (turns + "1", turns + "0") {
        if child in tree.vertices {
          line(name(turns) + ".east", name(child) + ".west")
        } else {
          let (x, y) = place(child)
          line(name(turns) + ".east", (x - dot-gap, y))
          for k in range(dot-count) {
            circle((x + k * dot-step, y), radius: 0.28, fill: black)
          }
        }
      }
    }
  }),
))
