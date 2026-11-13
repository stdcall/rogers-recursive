// The diagram of § 9.2: the branching computation of an oracle machine. Each
// question «w ∈ X?» of the computation splits it into the branch of the
// answer «Да» (up) and of the answer «Нет» (down); a branch ends with the end
// of the computation or goes on («…»).
#import "@preview/cetz:0.5.2": canvas, draw

// The example of the book: the first question is 7, then 11 on the branch
// «Да» and 17 on the branch «Нет».
#let oracle-tree = (
  question: 7,
  yes: (question: 11, yes: [Окончание], no: [. . . .]),
  no: (question: 17, yes: [. . .], no: [. . .]),
)

// Lengths in millimetres, from the printed drawing: the start, the slanted
// stroke of an answer, the run to the next question, the last run; the half
// spread of the answers at each level.
#let start-run = 13
#let slant = 4
#let question-run = 17
#let last-run = 10
#let spreads = (9, 5)

// The number of a question stands between its answers, «Да», «11», «Нет».
#let oracle-branching(tree) = align(center, block(
  above: 1em,
  below: 1em,
  canvas(length: 1mm, {
    import draw: *
    let label(body) = text(size: 8pt, style: "italic", body)
    let node(tree, x, y, level) = {
      content(
        (x + slant + 0.6, y),
        text(size: 8pt, weight: "bold", str(
          tree.question,
        )),
        anchor: "west",
      )
      for (side, key, word) in ((1, "yes", [Да]), (-1, "no", [Нет])) {
        let tip = (x + slant, y + side * spreads.at(level))
        line((x, y), tip, mark: (end: ">", fill: black, scale: 0.5))
        content(
          (tip.at(0) + 0.6, tip.at(1) - side * 1.8),
          label(word),
          anchor: "west",
        )
        let next = tree.at(key)
        if type(next) == dictionary {
          let end = (tip.at(0) + question-run, tip.at(1))
          line(tip, end)
          node(next, end.at(0), end.at(1), level + 1)
        } else {
          let end = (tip.at(0) + last-run, tip.at(1))
          line(tip, end)
          content((end.at(0) + 1, end.at(1)), label(next), anchor: "west")
        }
      }
    }
    content((-1, 0), $psi_z^X (x)$, anchor: "east")
    line((0, 0), (start-run, 0), mark: (end: ">", fill: black, scale: 0.5))
    content((1, -1.8), label[Начало], anchor: "west")
    node(tree, start-run, 0, 0)
  }),
))
