// All imports
#import "@preview/theoretic:0.2.0" as theoretic: theorem, proof, qed
#import "@preview/showybox:2.0.4": showybox
#import "@preview/fletcher:0.5.7" as fletcher: diagram, node, edge
// Main noteworthy function
#let noteworthy(
  paper-size: "a4",
  font: "New Computer Modern",
  language: "EN",
  title: none,
  author: none,
  chapter: none,
  toc-title: "Table of Contents",
  watermark: none,
  content,
) = {
  // Document metadata
  set document(
    title: [#title - #author],
    author: author,
    date: auto,
  )

  // Page settings
  set page(
    paper: paper-size,
    background: if watermark != none {
      rotate(-40deg, text(30pt, fill: rgb("FFCBC4"))[*#watermark*])
    },
    header: context {
      if (counter(page).get().at(0) > 1) [
        #grid(
          columns: (1fr, 1fr),
          align: (left, right),
          smallcaps(title), datetime.today().display("[day]/[month]/[year]"),
        )
        #line(length: 100%)
      ]
    },
    footer: context [
      #line(length: 100%)
      #grid(
        columns: (1fr, 1fr, 1fr),
        align: (left, center, right),
        author,
        if chapter != none {
          [#sym.diamond.filled Chapter #chapter #sym.diamond.filled]
        },
        counter(page).display(
          "(1/1)",
          both: true,
        ),
      )
    ],
  )

  // Text settings
  set text(
    font: font,
    size: 12pt,
    lang: language,
  )

  // TOC settings
  show outline.entry.where(level: 1): it => {
    v(12pt, weak: true)
    strong(it)
  }

  // Heading settings
  set heading(numbering: "1.")
  set math.equation(numbering: "(1)", number-align: bottom)
  set enum(numbering: "(i.a)")

  show ref: it => {
    let eq = math.equation
    let el = it.element
    if el != none and el.func() == eq {
      // Override equation references.
      link(el.location(),numbering(
        el.numbering,
        ..counter(eq).at(el.location())
      ))
    } else {
      // Other references as usual.
      it
    }
  }
  show math.equation: set block(breakable: true)
  // Paragraph settings
  set par(justify: true)

  // Title
  showybox(
    frame: (
      border-color: blue.darken(50%),
      body-color: blue.lighten(80%),
    ),
    shadow: (
      offset: 3pt,
    ),
    body-style: (
      align: center,
    ),
    text(weight: "black", size: 15pt, title),
  )

  // Table of contents
  showybox(
    outline(
      indent: auto,
      title: toc-title,
      depth: 2,
    ),
  )

  show ref: theoretic.show-ref
  // Main content
  content
}

// Custom environments using theoretic

// 1. Definition
#let definition = theorem.with(
  kind: "definition",
  supplement: "Definition",
  fmt-prefix: (s, n, t) => {
    text(weight: "bold", stretch: 85%)[#s #n]
    if t != none [ (#t)]
    h(1em)
  },
)

#let lemma = theorem.with(
  kind: "Lemma",
  supplement: "Lemma",
  fmt-prefix: (s, n, t) => {
    text(weight: "bold", stretch: 85%)[#s #n]
    if t != none [ (#t)]
    h(1em)
  },
)

#let proposition = theorem.with(
  kind: "Proposition",
  supplement: "Proposition",
  fmt-prefix: (s, n, t) => {
    text(weight: "bold", stretch: 85%)[#s #n]
    if t != none [ (#t)]
    h(1em)
  },
)

#let corollary = theorem.with(
  kind: "Corollary",
  supplement: "Corollary",
  fmt-prefix: (s, n, t) => {
    text(weight: "bold", stretch: 85%)[#s #n]
    if t != none [ (#t)]
    h(1em)
  },
)

// 2. Example
#let example = theorem.with(
  kind: "example",
  supplement: "Example",
  fmt-prefix: (s, n, t) => {
    text(weight: "bold", stretch: 85%)[#s #n]
    if t != none [ (#t)]
    h(1em)
  },
)

// 3. Theorem
#let theorem = theorem.with(
  fmt-prefix: (s, n, t) => {
    text(weight: "bold", stretch: 85%)[#s #n]
    if t != none [ (#t)]
    h(1em)
  },
)

// 4. Note
#let note = theorem.with(
  kind: "note",
  supplement: "Note",
  fmt-prefix: (s, n, t) => {
    text(weight: "bold", stretch: 85%)[#s #n]
    if t != none [ (#t)]
    h(1em)
  },
)

#let remark = theorem.with(
  kind: "remark",
  supplement: "Remark",
  fmt-prefix: (s, n, t) => {
    text(weight: "bold", stretch: 85%)[#s #n]
    if t != none [ (#t)]
    h(1em)
  },
)

#let sol(body) = {
  context[_Solution._]
  body
}