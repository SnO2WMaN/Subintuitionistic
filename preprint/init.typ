#import "@preview/ctheorems:1.1.3": *
#import "@preview/curryst:0.5.0": prooftree, rule

// Email addresses, ORCID iDs and URLs
#let mono(body) = text(font: "Liberation Mono", size: 0.75em, body)

// ---- 著者・所属 ----

// `institute` is a name or an array of names; authors sharing an institute share its number
#let author(name, institute: (), email: none, orcid: none) = {
  if type(institute) != array { institute = (institute,) }
  (name: name, insts: institute, email: email, orcid: orcid)
}

#let join-authors(items) = {
  if items.len() == 1 {
    items.first()
  } else if items.len() == 2 {
    items.join([ and ])
  } else {
    items.slice(0, -1).join([, ]) + [, and ] + items.last()
  }
}


#let thmnumber(target) = context {
  let el = query(target).first()
  let meta = query(selector(<meta:thmenvcounter>).after(el.location())).first()
  numbering(el.numbering, ..thmcounters.at(meta.location()).at("latest"))
}


// ---- 本体 ----

#let init(
  title: [],
  authors: (),
  abstract: none,
  date: none,
  body,
) = {
  // 脚注の中の `@thm:...` にも効かせるため，文書の最も外側で適用する
  show: thmrules.with(qed-symbol: [❏])

  set document(author: authors.map(a => a.name), title: title)
  if type(date) == datetime { set document(date: date) }
  // Noto Serif CJK SC sets the Chinese title of Che21 in the bibliography
  set text(font: ("New Computer Modern", "Libertinus Serif", "Noto Serif CJK SC"), lang: "en", size: 10pt)
  set par(leading: 0.5em, spacing: 0.75em)

  // The page layout of LaTeX's `article` class at 10pt on letter paper, as compiled by arXiv
  set page(
    paper: "us-letter",
    margin: (x: 120pt, top: 120pt, bottom: 120pt),
    numbering: "1",
  )

  set heading(numbering: "1.1")
  show heading: it => {
    // 見出し番号と本文の間隔は Typst 既定より広く取る
    let head = if it.numbering == none { it.body } else {
      counter(heading).display(it.numbering) + h(4.5mm) + it.body
    }
    if it.level == 1 {
      set text(12pt, weight: "bold")
      block(above: 18pt, below: 16pt, head)
    } else {
      set text(10pt, weight: "bold")
      block(above: 18pt, below: 8pt, head)
    }
  }

  set super(size: 8pt)
  // 9pt, not 0.9em: footnote entries are already set at 0.85em by default
  show footnote.entry: set text(9pt)
  set footnote.entry(
    separator: line(start: (0pt, 0pt), length: 57pt, stroke: 0.5pt),
    indent: 1mm,
  )

  set math.equation(numbering: none)
  show math.equation.where(block: true): set block(above: 1em, below: 1em)
  show math.equation: set text(font: ("New Computer Modern Math", "Libertinus Serif"))

  show link: set text(fill: color.hsl(234deg, 71.43%, 49.41%))

  // 中央寄せの証明図などは上下に余白を取る
  show align: set block(spacing: 1.2em)

  align(center, {
    block(text(size: 1.5em, title))

    v(11mm)

    let insts = authors.map(a => a.insts).flatten().dedup()

    join-authors(authors.map(a => {
      let refs = a.insts.map(i => str(insts.position(x => x == i) + 1)).join(",")
      [#a.name#super[#refs]]
    }))

    v(6mm)

    {
      set text(0.9em)
      set par(leading: 0.65em, spacing: 0.65em)
      insts.enumerate().map(((i, inst)) => [#super[#(i + 1)]#h(0.2em)#inst]).join(parbreak())

      // Email addresses and ORCID iDs, with the author's name when there are several authors
      for a in authors {
        let lines = ()
        if a.email != none { lines.push([Email: #link("mailto:" + a.email, mono(a.email))]) }
        if a.orcid != none { lines.push([ORCID: #link("https://orcid.org/" + a.orcid, mono(a.orcid))]) }
        if lines.len() > 0 {
          parbreak()
          if authors.len() > 1 [#a.name: ]
          lines.join(linebreak())
        }
      }
    }

    if date != none {
      v(6mm)
      if type(date) == datetime { date.display("[month repr:long] [day padding:none], [year]") } else { date }
    }

    if abstract != none {
      v(11mm)
      block(width: 85%, {
        set align(left)
        set par(justify: true)
        set text(0.9em)
        [*Abstract.* #abstract]
      })
    }
  })

  v(18pt)

  show figure.where(kind: "thmenv"): set par(first-line-indent: (all: false, amount: 1em))

  set par(justify: true, first-line-indent: (all: true, amount: 1em))

  body

  show std.bibliography: set text(0.9em)
  // Links in monospace. The CSL prints a URL as a bare link, which is lableved here "URL:"; an arXiv
  // abstract page is shown as "arXiv: 2309.05948" instead, since Hayagriva does not pass
  // `serial-number.arxiv` to the CSL. A rebuilt link sets only the font of its body, which stops the
  // recursion and leaves the size to `mono`.
  show std.bibliography: it => {
    show link: l => {
      let bare = (
        type(l.dest) == str and l.body.func() == text and l.body.text == l.dest and not l.body.has("font")
      )
      if not bare { return mono(l) }
      let id = l.dest.match(regex("^https://arxiv\.org/abs/(.+)$"))
      // the label replaces the original link, so it would take the link colour
      let rebuilt(body) = link(l.dest, text(font: "Liberation Mono", body))
      if id != none [#text(fill: black)[arXiv:] #rebuilt(id.captures.first())] else [#text(fill: black)[URL:] #rebuilt(
          l.dest,
        )]
    }
    it
  }
  bibliography("../references.yml", style: "style.csl")
}


// ---- 定理環境 ----
// 識別子を "theorem" で揃えているので，全環境が節ごとの通し番号を共有する

#let sqthmbox(title) = thmbox(
  "theorem",
  title,
  base: "heading",
  base_level: 1,
  inset: (top: 8pt, bottom: 8pt),
  radius: 0pt,
  titlefmt: strong,
  namefmt: name => strong[(#name)],
  separator: h(.4em),
  breakable: true,
)

#let definition = sqthmbox("Definition")
#let lemma = sqthmbox("Lemma")
#let theorem = sqthmbox("Theorem")
#let proposition = sqthmbox("Proposition")
#let corollary = sqthmbox("Corollary")
#let remark = sqthmbox("Remark")
#let example = sqthmbox("Example")

#let proof = thmproof(
  "proof",
  [_Proof._],
  // `thmproof` indents both sides by 1.2em by default; align it with the theorem environments
  inset: (x: 0em, top: 0em),
  // the default `emph` would turn the italic title upright
  titlefmt: it => it,
  separator: h(.4em),
)


// ================= Notations =================

// Upright text set letter by letter: a quoted string in math is set as text and gets a space
// before it (`tau "S"` would read "τ S").
#let mrm(s) = math.upright(eval(s.clusters().join(" "), mode: "math"))

#let proves = $class("relation", tack.r)$
// Derivability by a proof-tree of height at most `h`; `proves^h` would put `h` above the turnstile
#let provesh(h) = $attach(proves, tr: #h)$
#let forces = $class("relation", std.sym.forces)$

#let Box = $class("unary", square)$
#let lconj = $and.big$
#let ldisj = $or.big$

#let PropVar = $mrm("Prop")$
#let FmlPL = $mrm("Fml")_mrm("P")$
#let FmlML = $mrm("Fml")_mrm("M")$

#let Vis = $cal(V)$
#let God = $cal(G)$

#let Logic(L) = math.bold(mrm(L))
#let LogicGL = Logic("GL")
#let LogicD = Logic("D")
#let LogicS = Logic("S")
#let LogicK = Logic("K")
#let LogicKFour = Logic("K4")
#let LogicSFour = Logic("S4")
#let LogicInt = Logic("Int")
#let LogicBPL = Logic("BPL")
#let LogicFPL = Logic("FPL")
#let LogicDPL = Logic("DPL")
#let LogicSPL = Logic("SPL")

#let Theory(T) = math.bold(mrm(T))
#let TheoryPA = Theory("PA")
#let TheoryTA = Theory("TA")

// Levleved sequent arrows: `seq(1)`, `seq(lev)`
#let seq(l) = $attach(class("relation", =>), tr: #l)$
#let level = $ell$

#let Gentzen(L) = $sans(upright("G"))_(#L)$
#let GentzenS = Gentzen(LogicS)
#let GentzenD = Gentzen(LogicD)
#let GentzenSPL = Gentzen(LogicSPL)
#let GentzenDPL = Gentzen(LogicDPL)

// Names of rules: `RImpL(lev, lev)` is $(->"L"^lev_lev)$
#let rulename(n, a, b) = $paren.l attach(#n, tr: #a, br: #b) paren.r$
#let RAx(l) = $paren.l mrm("Ax")_#l paren.r$
#let RBotL(l) = $paren.l bot mrm("L")_#l paren.r$
#let RWL(a, b) = rulename(mrm("WL"), a, b)
#let RWR(a, b) = rulename(mrm("WR"), a, b)
#let RImpL(a, b) = rulename($class("normal", ->) mrm("L")$, a, b)
#let RImpR(a, b) = rulename($class("normal", ->) mrm("R")$, a, b)
#let RAndL(a, b) = rulename($class("normal", and) mrm("L")$, a, b)
#let RAndR(a, b) = rulename($class("normal", and) mrm("R")$, a, b)
#let ROrL(a, b) = rulename($class("normal", or) mrm("L")$, a, b)
#let ROrR(a, b) = rulename($class("normal", or) mrm("R")$, a, b)
#let RBoxL(a, b) = rulename($class("normal", square) mrm("L")$, a, b)
#let RBoxGL(a, b) = rulename($class("normal", square) LogicGL$, a, b)
#let RBoxKFour(a, b) = rulename($class("normal", square) LogicKFour$, a, b)
#let RLift(a, b) = rulename(mrm("LU"), a, b)
#let RCut(a, b) = rulename(mrm("Cut"), a, b)
#let Inv(x) = $#x^(-1)$


// ================= Proof trees =================

// A leaf with a small note above it, without a line (`\noLine` in bussproofs)
#let noted(note, x) = stack(
  dir: ttb,
  spacing: 0.35em,
  align(center, text(size: 0.7em, note)),
  x,
)
#let ih(x) = noted([(I.H.)], x)
// A leaf standing for a subtree, written above it without a line
#let subtree(name, x) = stack(dir: ttb, spacing: 0.35em, align(center, name), x)

// Rules or proof-trees side by side, aligned at the conclusions
#let side-by-side(align: center + bottom, ..xs) = std.align(center, grid(
  columns: xs.pos().len(),
  column-gutter: 2em,
  align: align,
  ..xs,
))
