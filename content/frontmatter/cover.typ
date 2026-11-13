// The front cover: pale pink cloth and one frame of dark green rules; in it
// the author at the top and the title at the foot, in a large roman ranged
// right, the conjunction «И» smaller. Places are given in the coordinates of
// a 309 × 500 drawing of the cover.
#import "../book-style.typ": page-height, page-width

#let cover-x(x) = x / 309 * page-width
#let cover-y(y) = y / 500 * page-height

#let cloth = rgb("efcdb9")
#let ink = rgb("576a3f")

// The frame, the right edge of the lettering, the baselines of the author and
// of the last line of the title, the left end of that line.
#let frame = (left: 40.5, top: 12.5, right: 293, bottom: 476.5)
#let text-right = 287
#let author-baseline = 39
#let title-baseline = 470
#let title-left = 45

#let title-lines = (
  [ТЕОРИЯ],
  [РЕКУРСИВНЫХ],
  [ФУНКЦИЙ],
  text(size: 0.78em)[И],
  [ЭФФЕКТИВНАЯ],
  [ВЫЧИСЛИМОСТЬ],
)

#let cover() = page(
  width: page-width,
  height: page-height,
  margin: 0pt,
  header: none,
  footer: none,
  fill: cloth,
  numbering: none,
  {
    place(dx: cover-x(frame.left), dy: cover-y(frame.top), rect(
      width: cover-x(frame.right - frame.left),
      height: cover-y(frame.bottom - frame.top),
      stroke: 2pt + ink,
    ))
    set text(
      font: "Libertinus Serif",
      size: 35pt,
      fill: ink,
      // The printed letters are heavier than the regular cut and lighter
      // than the bold: a hairline stroke gives their weight.
      stroke: 0.7pt + ink,
      lang: "ru",
      top-edge: "cap-height",
      bottom-edge: "baseline",
    )
    set par(first-line-indent: 0pt, justify: false, leading: cover-y(6))
    // The letters are spaced so that the longest line of the title fills its
    // printed width; the author is spaced as printed, wider.
    context {
      let longest = measure(title-lines.last()).width
      let spacing = (
        (cover-x(text-right - title-left) - longest) / (12 - 1)
      )
      let title = align(right, text(tracking: spacing, title-lines.join(
        linebreak(),
      )))
      let title-height = measure(
        block(width: page-width, title),
      ).height
      place(
        top + right,
        dx: -cover-x(309 - text-right),
        dy: cover-y(title-baseline) - title-height,
        title,
      )
      let author = text(tracking: 0.22em)[Х·РОДЖЕРС]
      place(
        top + right,
        dx: -cover-x(309 - text-right),
        dy: cover-y(author-baseline) - measure(author).height,
        author,
      )
    }
  },
)
