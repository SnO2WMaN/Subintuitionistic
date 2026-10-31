#import "init.typ": *

#show: init.with(
  title: [Embeddings of Propositional Logics into the Provability Logics $LogicS$ and $LogicD$],
  authors: (
    author(
      "Mashū Noguchi",
      institute: "Graduate School of System Informatics, Kobe University",
      email: "me@sno2wman.net",
      orcid: "0009-0000-8653-3403",
    ),
  ),
  date: datetime.today(),
  abstract: [
    Just as Visser showed that the formal propositional logic $LogicFPL$ can be embedded into Gödel-Löb provability logic $LogicGL$,
    Petrukhin proposed a propositional logic $LogicSPL$ that can be embedded into Solovay's non-normal provability logic $LogicS$.
    In this paper, we fix Petrukhin's proof and
    extend the result to Japaridze's provability logic $LogicD$,
    and propose a propositional logic $LogicDPL$ that can be embedded into $LogicD$.
  ],
)

= Introduction

In 1976, Solovay @Sol76 proved the arithmetical completeness theorem, which is a fundamental landmark result in provability logic.
More precisely, he proved that a modal formula is provable in the logic $LogicGL$ if and only if
every arithmetical sentence, obtained from the modal formula by interpreting the propositional variables as arithmetical sentences
and the modal operator $Box$ as an appropriate provability predicate $mrm("Pr")_TheoryPA (x)$ of $TheoryPA$, is provable in $TheoryPA$.
As an extension of this result, he also showed that a non-normal extension of $LogicGL$, known as $LogicS$, is arithmetically complete with respect to
true arithmetic $TheoryTA$.
Furthermore, Japaridze (also transliterated as Dzhaparidze) discovered a provability logic $LogicD$
that is strictly intermediate between $LogicGL$ and $LogicS$ in his thesis @Jap86.
The logic $LogicD$ is the provability logic of $TheoryPA$ relative to $TheoryPA + mrm("Rfn")_TheoryPA (Sigma_1)$,
that is, any modal formula is provable in $LogicD$ if and only if
every arithmetical sentence obtained from the formula by above interpretation is provable in $TheoryPA + mrm("Rfn")_TheoryPA (Sigma_1)$.
Here, $mrm("Rfn")_TheoryPA (Sigma_1)$ denotes the reflection principle for $Sigma_1$-sentences.
Subsequently, Beklemishev @Bek87 proved the classification theorem for provability logics,
which states that every provability logic must belong to one of four families of logics,
each being an appropriate extension of one of $LogicGL$, $LogicS$, or $LogicD$.
For more results and detailed discussions about $LogicD$ and the classification theorem,
see Beklemishev's papers @Bek87 @Bek89 @Bek90 or the survey by Artemov and Beklemishev @AB05.

// The semantics completeness of $LogicGL$ with respect to Kripke semantics was established by Segerberg @Seg71.
// However, since $LogicS$ is a non-normal, a straightforward Kripke-semantical treatment for $LogicS$ is not available.
// Visser @Vis84 showed that it corresponds naturally to a class of models called tail models
// which are obtained by appending an appropriate $(omega + 1)$-many points to models of $LogicGL$.

Sequent calculi for provability logics have been wlev studied, particularly for $LogicGL$ @Lei81 @SV82 @Val83 @Bor83 @Avr84 @Moe01 @GR12 @Bri16 @GRS21.
Kushida @Kus20 proposed a new sequent calculus for $LogicS$, which has two levels of sequents $seq(1)$ and $seq(2)$,
and proved cut-elimination for the calculus.
Roughly speaking, sequents with $seq(1)$ correspond to provability in $LogicGL$ and sequents with $seq(2)$ correspond to provability in $LogicS$.
There is a lift-up rule from $seq(1)$ to $seq(2)$, but not vice versa.
Extending this approach, Kashima et al. @KKIM25 proposed a new sequent calculus for $LogicD$,
which has three levels of sequents $seq(1)$, $seq(2)$ and $seq(3)$.
Sequents with $seq(1)$ and $seq(2)$ correspond to provability in $LogicGL$ and $LogicS$, respectively, and sequents with $seq(3)$ correspond to provability in $LogicD$.

Another wlev-known result, due to Gödel, McKinsey and Tarski @God33 @MT48,
is that provability in propositional intuitionistic logic $LogicInt$ can be interpreted as provability in the modal logic $LogicSFour$
via a translation known as Gödel translation.
When such a correspondence holds, the modal logic is called a _modal companion_ of the propositional logic
(for instance, $LogicSFour$ is a modal companion of $LogicInt$).
It is wlev known which modal logics are the modal companions of logics stronger than $LogicInt$, that is, of superintuitionistic logics
(see @CZ97).
On the other hand, it has also been investigated which propositional logics have modal companions weaker than or incomparable to $LogicSFour$.
Visser @Vis81 found two propositional logics whose modal companions, via a modified Gödel translation, are $LogicKFour$ and $LogicGL$, respectively,
and named them Basic Propositional Logic $LogicBPL$ and Formal Propositional Logic $LogicFPL$.
Simple sequent calculi for $LogicBPL$ and $LogicFPL$ were proposed by Ishii et al. @IKK01.
Yamasaki and Sano @YS17 modified their sequent calculus for $LogicBPL$ into a G3-style sequent calculus
and investigated its proof-theoretic properties.
Moreover, they showed the embedding of $LogicBPL$ into $LogicKFour$ via the modified Gödel translation syntactically
by means of analytic proofs.
We also note that, in the direction opposite to ours, Chen @Che21 discussed such an embedding for the logic $Logic("F")$ introduced by Corsi @Cor87, which is weaker than $LogicBPL$ and corresponds to the modal logic $LogicK$.

Petrukhin @Pet23 combined the idea of Kushida's two-level sequent calculus for $LogicS$ with a sequent calculus for $LogicFPL$,
proposing a sequent calculus for a propositional logic with two levels of sequents,
and he named the propositional logic obtained from this sequent calculus Solovay Propositional Logic $LogicSPL$.
Furthermore, by employing the method of Yamasaki and Sano,
he claims that the sequent calculus for $LogicSPL$ can be syntactically embedded into Kushida's sequent calculus for $LogicS$ via the modified Gödel translation,
that is, $LogicS$ is a modal companion of $LogicSPL$.
However, Petrukhin's proof appears to contain some errors,
and it seems that straightforward corrections are insufficient to fix them.

This paper is devoted to two objectives.
The first is to provide a complete and detailed proof from scratch that $LogicS$ is the modal companion of $LogicSPL$,
and in the course of doing so, to identify the errors in Petrukhin's paper.
For the sequent calculus of $LogicS$, we use not Kushida's original calculus
but a further modification of the one corrected by Kashima et al. @KK23.
The second objective is to define a sequent calculus for a propositional logic,
which we name Dzhaparidze Propositional Logic $LogicDPL$.
The sequent calculus for $LogicDPL$ has three levels of sequents,
and is obtained by adding to the sequent calculus for $LogicSPL$ one rule which arises naturally from the sequent calculus for $LogicD$.
Then we show, by a slight adaptation of the proof we gave for $LogicSPL$,
that $LogicDPL$ can be embedded into $LogicD$, that is, $LogicD$ is a modal companion of $LogicDPL$.

/*
This paper is organized as follows.
In @sect:preliminaries, we introduce some notations and definitions that are used throughout the paper and mention some basic facts.
In @sect:GentzenS, we define a sequent calculus $GentzenS$ for $LogicS$
and show some syntactic results from @Kus20 @KK23.
In @sect:GentzenSPL, we define a sequent calculus $GentzenSPL$ for $LogicSPL$.
In @sect:Embedding_GentzenSPL_GentzenS, we show that $GentzenSPL$ can be embedded into $GentzenS$ via the modified Gödel translation.
Additionally, we mention some errors in Petrukhin's proof in @sect:errors_in_Petrukhin.
In @sect:GentzenD, we define a sequent calculus $GentzenD$ for $LogicD$ from @KKIM25.
In @sect:GentzenDPL, we define a sequent calculus $GentzenDPL$ for $LogicDPL$.
In @sect:Embedding_GentzenDPL_GentzenD, we show that $GentzenDPL$ can be embedded into $GentzenD$ via the modified Gödel translation
by modifying the proof in @sect:Embedding_GentzenSPL_GentzenS.
Finally, we give some concluding remarks and open problems in @sect:conclusion.
*/

== Acknowledgements

The author would like to thank Kohei Tominaga, Naoyuki Hatanaka, Haruka Kogure, and Taishi Kurahashi
for carefully reading the first draft of this paper
and providing valuable discussions and corrections of minor errors.

== Use of AI

The author declares that AI/LLMs were involved in the preparation of this paper.
/*
While writing this draft, a review by Claude Fable pointed out a fatal error
in a part of the proof in @sect:Embedding_GentzenSPL_GentzenS as originally given.
This part was fixed with Claude, and the resulting arguments were verified by the author.
Any remaining errors are the sole responsibility of the author.
*/

== Revision notes

// TODO
 
= Preliminaries <sect:preliminaries>

In this section, we introduce some notations and definitions that are used throughout the paper and mention some basic facts.
For more details, refer to the standard textbooks such as @Boo94 @CZ97.

Propositional variables are denoted by lowercase letters $p, q, r, dots$, and the set of all propositional variables is denoted by $PropVar$.
Formulas of propositional logic are constructed from propositional variables by the logical connectives $bot, and, or, ->$.
Formulas of modal logic are constructed from propositional variables by $bot, ->$ and the modal operator $Box$.
Other connectives are defined as usual:

$
    not A := A -> bot, quad top := not bot, quad A and B := not (A -> not B), quad A or B := not A -> B.
$

Formulas of both propositional logic and modal logic are denoted by uppercase letters $A, B, C, dots$.
We write $FmlPL$ for the set of all formulas of propositional logic, and $FmlML$ for the set of all formulas of modal logic.
For our purpose, uppercase Greek letters $Gamma, Delta, dots$ denote _sets_ of formulas.
For a set $Gamma$ of modal formulas, we write $Box Gamma$ for the set ${Box A : A in Gamma}$.
Moreover, for a finite set $Gamma$, we write $lconj Gamma$ and $ldisj Gamma$ for the conjunction and the disjunction of all elements of $Gamma$,
respectively, where the empty conjunction $lconj emptyset$ and the empty disjunction $ldisj emptyset$ are understood as $top$ and $bot$.

Modal logic $LogicGL$ (stands for Gödel--Löb) is the smallest normal modal logic containing the axiom $Box (Box A -> A) -> Box A$.
Solovay's modal logic $LogicS$ is a non-normal extension of $LogicGL$ with the axiom $Box A -> A$;
that is, $LogicS$ is the smallest set of formulas that contains all theorems of $LogicGL$ and all instances of $Box A -> A$, and is closed under modus ponens only (but not under necessitation).
Japaridze's modal logic $LogicD$ is the non-normal extension of $LogicGL$ with the axioms $Box (Box A or Box B) -> Box A or Box B$ and $not Box bot$, defined analogously.
The following proposition can be shown by using the semantic tools for $LogicS$ and $LogicD$ developed in @Vis84 @Bek89.

#proposition[
  $LogicGL subset.neq LogicD subset.neq LogicS$.
  That is, $LogicGL proves A$ implies $LogicD proves A$, and $LogicD proves A$ implies $LogicS proves A$, but the converses do not hold.
]

The Gödel translation is well-known embedding of intuitionistic propositional logic into modal logic.

#definition[Gödel translation][
  Gödel translation $(dot)^God : FmlPL -> FmlML$ is defined as follows.
  $
   p^God &equiv Box p \
   bot^God &equiv Box bot \
   (A and B)^God &equiv A^God and B^God \
   (A or B)^God &equiv A^God or B^God \
   (A -> B)^God &equiv Box (A^God -> B^God) \
$
  For a set $Gamma$ of propositional formulas, we write $Gamma^God$ for the set ${A^God : A in Gamma}$.
] <defn:visser>

However, for our purpose, we need another translation, introduced by Visser @Vis81, which we call Visser--Gödel translation.

#definition[Visser--Gödel translation @Vis81][
  Visser--Gödel translation $(dot)^Vis : FmlPL -> FmlML$ is defined as follows.
  $
   p^Vis &equiv p and Box p \
   bot^Vis &equiv bot \
   (A and B)^Vis &equiv A^Vis and B^Vis \
   (A or B)^Vis &equiv A^Vis or B^Vis \
   (A -> B)^Vis &equiv Box (A^Vis -> B^Vis) \
$
  For a set $Gamma$ of propositional formulas, we write $Gamma^Vis$ for the set ${A^Vis : A in Gamma}$.
] <defn:visser>

#remark[
ここで注意して置くこととして，我々は様相論理の論理結合子を $->, bot$ による略記として導入しているから，実際にはVisser--Gödel変換は命題論理式の見かけ上とは異なることに留意しなければならない．

$
  p^Vis & equiv (p -> (Box p -> bot)) -> bot, \
  (A and B)^Vis & equiv (A^Vis -> (B^Vis -> bot)) -> bot, \
 (A or B)^Vis  & equiv (A^Vis -> bot) -> B^Vis.
$

このことは証明論的な埋め込みを考えるうえでは非常にデリケートな問題になる．
]

@Vis81 は次のことをKripke意味論を用いて示した．

#proposition[@Vis81[Theorem 5.2]][
  Let $A in FmlPL$. These following are equivalent.
  1. $LogicFPL proves A$. 
  2. $LogicGL proves A^Vis$.
  3. $LogicGL proves A^God$.
]

詳しくは @subsect:proof_theoritcal_embedding で解説するように，この事実は @YS17 の方法によって証明論的な方法によっても示すことが出来る．

/*
Finally, we fix the proof-theoretic terminology used throughout this paper.
For the sequent calculi introduced in the following sections,
the notions of a derivation and its height, and of (height-preserving) admissible rules,
are defined as usual (see e.g. @TS00 @NvP11).
We write $sans(upright(G)) proves S$ if a sequent $S$ is derivable in a sequent calculus $sans(upright(G))$,
and $sans(upright(G)) provesh(h) S$ if $S$ is derivable in $sans(upright(G))$ by a derivation of height at most $h$.
For a formula $A$ and sets $Gamma, Delta$ of formulas, in the context of sequents,
we write $A, Gamma$ for ${A} union Gamma$ and $Gamma, Delta$ for $Gamma union Delta$.
Note that $A, Gamma = Gamma$ when $A in Gamma$, so that contraction is built into this notation.
*/

== Sequent calculus for modal provability logics

Although Kushida @Kus20 first introduced a sequent calculus for $LogicS$, his formulation is not suitable for our purpose.
我々は @KKIM25 の $LogicD$ のためのアプローチを少し修正して採用する．
その部分体系は $LogicS$ のシークエント計算になっている．
このサブセクションでは導入と，いくらかの証明論的な性質を述べておく．

#definition[
  Let $Gamma, Delta$ be sets of formulas and let $level = 1, 2, 3$.
  An expression of the form $Gamma seq(level) Delta$ is called a _sequent_.

  The sequent calculus $GentzenD$ for $LogicD$, in which sequents of level $level = 1, 2, 3$ is defined by the following rules.
  
  #grid(
    columns: (1fr, 1fr),
    row-gutter: 1.5em,
    column-gutter: 2em,
    align: center + horizon,
    [
      #prooftree(rule(name: $RAx(level)$, $p seq(level) p$))
      where $p in PropVar$.
    ],
    prooftree(rule(name: $RBotL(level)$, $bot seq(level)$)),

    grid.cell(
      colspan: 2,
    prooftree(rule(name: $RWk(level, level)$, $Gamma' seq(level) Delta'$, $Gamma seq(level) Delta$)),
   
    ),
     prooftree(rule(name: $RLift(1, 2)$, $Gamma seq(2) Delta$, $Gamma seq(1) Delta$)),

    prooftree(rule(name: $RLift(2, 3)$, $Box Gamma seq(3) Box Delta$, $Box Gamma seq(2) Box Delta$)),
   
    prooftree(rule(
      name: $RImpL(level, level)$,
      $A -> B, Gamma seq(level) Delta$,
      $Gamma seq(level) Delta, A$,
      $B, Gamma seq(level) Delta$,
    )),
    prooftree(rule(name: $RImpR(level, level)$, $Gamma seq(level) Delta, A -> B$, $A, Gamma seq(level) Delta, B$)),
 
      prooftree(rule(name: $RBoxGL(1, 1)$, $Box Gamma seq(1) Box A$, $Box Gamma, Gamma, Box A seq(1) A$)),  
      prooftree(rule(name: $RBoxL(2, 2)$, $Box A, Gamma seq(2) Delta$, $A, Gamma seq(2) Delta$)),
  )
] <def:GentzenD>

For the above calculi, we note that the provability of $seq(1)$ is the same as that of the sequent calculus for $LogicGL$ (cf. @SV82).

@KKIM25 ではinitial sequentは任意の論理式 $A$ として $A seq(level) A$ によって導入されているが，ここでは $RAx(ell)$ を命題変数のみに制限していることに注意しておこう．
ただし，これは単に次章において証明論的な埋め込みを考えるためのテクニカルな修正であり，実際には以下の補題より @KKIM25 と同等の証明能力を持っていると見做して良い．

#lemma[
  For any $A in FmlML$ and $level = 1, 2, 3$, $GentzenD proves A seq(ell) A$.
] <lem:GentzenS_original_axioms>

#proof[
  We show by induction on $A$, uniformly in $ell = 1, 2$.
  If $A equiv p$, the claim follows from $RAx(ell)$.
  If $A equiv bot$, it follows from $RBotL(ell)$ and $RWR(ell, ell)$.
  The case $A equiv B -> C$ is proved by the following derivation:
  $
    #prooftree(rule(
      name: $RImpR(ell, ell)$,
      $B -> C seq(ell) B -> C$,
      rule(
        name: $RImpL(ell, ell)$,
        $B -> C, B seq(ell) C$,
        rule(name: $RWR(ell, ell)$, $B seq(ell) C, B$, ih($B seq(ell) B$)),
        rule(name: $RWk(ell, ell)$, $C, B seq(ell) C$, ih($C seq(ell) C$)),
      ),
    ))
  $

  The case $A equiv Box B$ is proved by the following derivation:
  $
    #prooftree(rule(
      name: $RBoxGL(1, 1)$,
      $Box B seq(1) Box B$,
      rule(name: $RWk(1, 1)$, $B, Box B seq(1) B$, ih($B seq(1) B$)),
    ))
  $
  When $level = 2$, we apply $RLift(1, 2)$ to obtain $Box B seq(2) Box B$.
  Moreover, when $level = 3$, we can apply $RLift(2, 3)$ to $Box B seq(2) Box B$ because antescent and succedent are $Box B$ form, so we can obtain $Box B seq(3) Box B$.
]

この同値性より，@KKIM25 で示されている以下の事実を用いることが出来る．

#proposition[Provability of $GentzenD$ @KKIM25[Proposition 3.5]][
  The following equivalences hold for $GentzenD$.
  + $GentzenD proves Gamma seq(1) Delta$ iff $LogicGL proves lconj Gamma -> ldisj Delta$.
  + $GentzenD proves Gamma seq(2) Delta$ iff $LogicS proves lconj Gamma -> ldisj Delta$.
  + $GentzenD proves Gamma seq(2) Delta$ iff $LogicD proves lconj Gamma -> ldisj Delta$.
] <prop:GentzenS_provability>

#proposition[Cut-admissibility of $GentzenD$][
  The cut rule is admissible in $GentzenD$.
  That is, when the cut rule $RCut(ell, ell)$ is defined as below, if $GentzenD + RCut(ell, ell) proves Gamma seq(ell) Delta$ then $GentzenD proves Gamma seq(ell) Delta$.
  $
    #prooftree(rule(
      name: $RCut(ell, ell)$,
      $Gamma_1, Gamma_2 seq(ell) Delta_1, Delta_2$,
      $Gamma_1 seq(ell) Delta_1, A$,
      $A, Gamma_2 seq(ell) Delta_2$,
    ))
  $
] <prop:GentzenS_cut_elimination>

Note that cut-admissibility is proved by semantical tools, not syntactical way.

#lemma[
  $GentzenD$ で，各 $ell = 1, 2, 3$ について次の規則 $RAndL(level, level), RAndR(level, level), ROrL(level, level), ROrR(level, level)$ はadmissible．

  #grid(
    columns: (1fr, 1fr),
    row-gutter: 1.5em,
    column-gutter: 2em,
    align: center + horizon,
    prooftree(rule(name: $RAndL(level, level)$, $A and B, Gamma seq(level) Delta$, $A, B, Gamma seq(level) Delta$)),
    prooftree(rule(
      name: $RAndR(level, level)$,
      $Gamma seq(level) Delta, A and B$,
      $Gamma seq(level) Delta, A$,
      $Gamma seq(level) Delta, B$,
    )),

    prooftree(rule(
      name: $ROrL(level, level)$,
      $A or B, Gamma seq(level) Delta$,
      $A, Gamma seq(level) Delta$,
      $B, Gamma seq(level) Delta$,
    )),
    prooftree(rule(name: $ROrR(level, level)$, $Gamma seq(level) Delta, A or B$, $Gamma seq(level) Delta, A, B$)),
  )
] <lem:derived>

#proof[
  $A and B equiv (A -> (B -> bot)) -> bot$，$A or B equiv (A -> bot) -> B$ であることに注意してRoutine  work．
]

= Syntactical Embedding

$LogicS$ および $LogicD$ に $(dot)^Vis$ 変換で対応する論理 $LogicSPL$ (Solovay propositional logic) および $LogicDPL$ (Dz propositional logic) をシークエント計算によってそれぞれ定める．

#definition[Sequent calculi $GentzenDPL$][
  Let $Gamma, Delta$ be finite sets of formulas in $FmlPL$ and let $level = 1, 2, 3$.
  The sequent calculus $GentzenDPL$ for $LogicDPL$ consists of the following initial sequents and rules, where $level = 1, 2, 3$ is arbitrary unless otherwise stated.

  #grid(
    columns: (1fr, 1fr),
    row-gutter: 1.5em,
    column-gutter: 2em,
    align: center + horizon,
    [
      #prooftree(rule(name: $RAx(level)$, $p seq(level) p$))
      where $p in PropVar$.
    ],
    prooftree(rule(name: $RBotL(level)$, $bot seq(level)$)),

    grid.cell(
      colspan: 2,
    [
      #prooftree(rule(name: $RWk(level, level)$, $Gamma' seq(level) Delta'$, $Gamma seq(level) Delta$))
      where $Gamma subset.eq Gamma'$ and $Delta subset.eq Delta'$.
    ],
    ),
    prooftree(rule(name: $RAndL(level, level)$, $A and B, Gamma seq(level) Delta$, $A, B, Gamma seq(level) Delta$)),
    prooftree(rule(
      name: $RAndR(level, level)$,
      $Gamma seq(level) Delta, A and B$,
      $Gamma seq(level) Delta, A$,
      $Gamma seq(level) Delta, B$,
    )),

    prooftree(rule(
      name: $ROrL(level, level)$,
      $A or B, Gamma seq(level) Delta$,
      $A, Gamma seq(level) Delta$,
      $B, Gamma seq(level) Delta$,
    )),
    prooftree(rule(name: $ROrR(level, level)$, $Gamma seq(level) Delta, A or B$, $Gamma seq(level) Delta, A, B$)),

    grid.cell(
      colspan: 2,
      [
        #prooftree(rule(
          name: $RImpR(1, 1)$,
          $Gamma, \{C_i -> D_i : i < k \} seq(1) A -> B$,
          $Delta_I, Gamma, A -> B, A seq(1) B, Gamma_I quad (I subset.eq {0, dots, k - 1})$,
        ))
        where $k >= 0$, $C_0 -> D_0, ..., C_(k - 1) -> D_(k - 1)$ are arbitary and set $Delta_I := {D_j : j in I}$ and $Gamma_I := {C_j : j in.not I}$.
        Note that the number of premises is $2^k$. 
      ],
    ),
    grid.cell( 
      prooftree(rule(
        name: $RImpL(2, 2)$,
        $A -> B, Gamma seq(2) Delta$,
        $Gamma seq(2) Delta, A$,
        $B, Gamma seq(2) Delta$,
      )),
    ),

    prooftree(rule(name: $RLift(1, 2)$, $Gamma seq(2) Delta$, $Gamma seq(1) Delta$)),
    grid.cell( 
      colspan: 2,
      [
        #prooftree(rule(
          name: $RLift(2, 3)$,
          $\{A_i -> B_i : i < n\}, Phi seq(3) {C_j -> D_j : j < m}$,
          $\{A_i -> B_i : i < n\}, Phi seq(2) {C_j -> D_j : j < m}$,
        ))
        where $n, m >= 0$, $A_i, B_i, C_j, D_j in FmlPL$, and $Phi$ is a finite subset of $PropVar$.
      ],
    ),

  )
]

#example[
  The rule $RImpR(1, 1)$ for $k = 0, 1, 2$ takes the following forms.

  $k = 0$:
  $
    #prooftree(rule(name: $RImpR(1, 1)$, $Gamma seq(1) A -> B$, $Gamma, A -> B, A seq(1) B$))
  $

  $k = 1$:
  $
    #prooftree(rule(
      name: $RImpR(1, 1)$,
      $Gamma, C_0 -> D_0 seq(1) A -> B$,
      $D_0, Gamma, A -> B, A seq(1) B$,
      $Gamma, A -> B, A seq(1) B, C_0$,
    ))
  $

  $k = 2$:
  #wide(prooftree(rule(
    name: $RImpR(1, 1)$,
    $Gamma, C_0 -> D_0, C_1 -> D_1 seq(1) A -> B$,
    $D_0, D_1, Gamma, A -> B, A seq(1) B$,
    $D_0, Gamma, A -> B, A seq(1) B, C_1$,
    $D_1, Gamma, A -> B, A seq(1) B, C_0$,
    $Gamma, A -> B, A seq(1) B, C_0, C_1$,
  )))
] <ex:GentzenDPL_ImpR>

これらの準備の上で，論理式の集合として論理 $LogicSPL$ と $LogicDPL$ を定める．

#definition[
  We define _Solovay Propositional Logic_ $LogicSPL$ and  _Dzhaparidze Propositional Logic_ $LogicDPL$. 
  - $LogicSPL := {A in FmlPL : GentzenDPL proves seq(2) A}$. 
  - $LogicDPL := {A in FmlPL : GentzenDPL proves seq(3) A}$. 
]

#lemma[
  For every $A in FmlPL$ and $level = 1, 2, 3$, $GentzenDPL proves A seq(ell) A$.
] <lem:GentzenDPL_axioms>

#proof[
  We show the claim by induction on $A$, simultaneously for $level = 1, 2, 3$.
  If $A equiv p$, the claim is $RAx(ell)$.
  If $A equiv bot$, apply $RWk(ell, ell)$ to $RBotL(ell)$.
  If $A equiv B and C$, we have the following derivation.
  $
    #prooftree(rule(
      name: $RAndR(ell, ell)$,
      $B and C seq(ell) B and C$,
      rule(
        name: $RAndL(ell, ell)$,
        $B and C seq(ell) B$,
        rule(name: $RWk(ell, ell)$, $B, C seq(ell) B$, ih($B seq(ell) B$)),
      ),
      rule(
        name: $RAndL(ell, ell)$,
        $B and C seq(ell) C$,
        rule(name: $RWk(ell, ell)$, $B, C seq(ell) C$, ih($C seq(ell) C$)),
      ),
    ))
  $
  If $A equiv B or C$, we have the following derivation.
  $
    #prooftree(rule(
      name: $ROrL(ell, ell)$,
      $B or C seq(ell) B or C$,
      rule(
        name: $ROrR(ell, ell)$,
        $B seq(ell) B or C$,
        rule(name: $RWk(ell, ell)$, $B seq(ell) B, C$, ih($B seq(ell) B$)),
      ),
      rule(
        name: $ROrR(ell, ell)$,
        $C seq(ell) B or C$,
        rule(name: $RWk(ell, ell)$, $C seq(ell) B, C$, ih($C seq(ell) C$)),
      ),
    ))
  $
  If $A equiv B -> C$, we first derive $B -> C seq(1) B -> C$ by the following instance of $RImpR(1, 1)$ for $k = 1$ with $Gamma = emptyset$ and $C_0 -> D_0 := B -> C$.
  $
    #prooftree(rule(
      name: $RImpR(1, 1)$,
      $B -> C seq(1) B -> C$,
      rule(name: $RWk(1, 1)$, $C, B -> C, B seq(1) C$, ih($C seq(1) C$)),
      rule(name: $RWk(1, 1)$, $B -> C, B seq(1) C, B$, ih($B seq(1) B$)),
    ))
  $
  When $ell = 2, 3$, we further apply $RLift(1, 2)$, and when $ell = 3$ we apply $RLift(2, 3)$ to $B -> C seq(2) B -> C$ with $n = m = 1$ and $Phi = emptyset$, which is applicable since both sides consist of implications.
]

== Main reults <subsect:proof_theoritcal_embedding>

We give a detailed proof of the embedding of $GentzenDPL$ into $GentzenD$ based on the proofs in @YS17 @Pet23.

#lemma[
  The following rule $RBoxKFour(1, ell)$ is admissible in $GentzenD$.
  $
    #prooftree(rule(name: $RBoxKFour(1, ell)$, $Box Gamma seq(ell) Box A$, $Box Gamma, Gamma seq(1) A$))
  $
] <lem:GentzenS_admits_BoxK4>

#proof[
  For $ell = 1$, the claim is proved by the following derivation:
  $
    #prooftree(rule(
      name: $RBoxGL(1, 1)$,
      $Box Gamma seq(1) Box A$,
      rule(name: $RWk(1, 1)$, $Gamma, Box Gamma, Box A seq(1) A$, $Gamma, Box Gamma seq(1) A$),
    ))
  $
  When $ell = 2, 3$, we further apply $RLift(1, 2)$ and $RLift(2, 3)$ to obtain $Box Gamma seq(level) Box A$.
]

#lemma[cf. @YS17[Lemma 3]][
  For every $A in FmlPL$ and $level = 1, 2, 3$, $GentzenD proves A^Vis seq(ell) Box A^Vis$.
] <lem:embedding_SPL_to_S_aux1>

#proof[
  We show by induction on $A$. The cases $A equiv bot$ and $A equiv B or C$ are omitted.

  *Case* $A equiv p$:
  $
    #prooftree(rule(
      name: $RAndL(ell, ell)$,
      $p and Box p seq(ell) Box (p and Box p)$,
      rule(
        name: $RWk(ell, ell)$,
        $p, Box p seq(ell) Box (p and Box p)$,
        rule(
          name: $RBoxKFour(1, ell)$,
          $Box p seq(ell) Box (p and Box p)$,
          rule(
            name: $RAndR(1, 1)$,
            $Box p, p seq(1) p and Box p$,
            noted([(@lem:GentzenS_original_axioms, $RWk(1, 1)$)], $Box p, p seq(1) p$),
            noted([(@lem:GentzenS_original_axioms, $RWk(1, 1)$)], $Box p, p seq(1) Box p$),
          ),
        ),
      ),
    ))
  $

  *Case* $A equiv B and C$:
  $
    #prooftree(rule(
      name: $RAndL(ell, ell)$,
      $B^Vis and C^Vis seq(ell) Box (B^Vis and C^Vis)$,
      rule(
        name: $RCut(ell, ell)$,
        $B^Vis, C^Vis seq(ell) Box (B^Vis and C^Vis)$,
        rule(
          name: $RAndR(ell, ell)$,
          $B^Vis, C^Vis seq(ell) Box B^Vis and Box C^Vis$,
          rule(name: $RWk(ell, ell)$, $B^Vis, C^Vis seq(ell) Box B^Vis$, ih($B^Vis seq(ell) Box B^Vis$)),
          rule(name: $RWk(ell, ell)$, $B^Vis, C^Vis seq(ell) Box C^Vis$, ih($C^Vis seq(ell) Box C^Vis$)),
        ),
        rule(
          name: $RAndL(ell, ell)$,
          $Box B^Vis and Box C^Vis seq(ell) Box (B^Vis and C^Vis)$,
          rule(
            name: $RBoxKFour(1, ell)$,
            $Box B^Vis, Box C^Vis seq(ell) Box (B^Vis and C^Vis)$,
            rule(
              name: $RAndR(1, 1)$,
              $B^Vis, C^Vis, Box B^Vis, Box C^Vis seq(1) B^Vis and C^Vis$,
              noted(
                [(@lem:GentzenS_original_axioms, $RWk(1, 1)$)],
                $B^Vis, C^Vis, Box B^Vis, Box C^Vis seq(1) B^Vis$,
              ),
              noted(
                [(@lem:GentzenS_original_axioms, $RWk(1, 1)$)],
                $B^Vis, C^Vis, Box B^Vis, Box C^Vis seq(1) C^Vis$,
              ),
            ),
          ),
        ),
      ),
    ))
  $
  Here the use of the cut rule $RCut(ell, ell)$ is legitimate by @prop:GentzenS_cut_elimination; we use the cut rule freely in derivations in what follows.

  *Case* $A equiv B -> C$:
  $
    #prooftree(rule(
      name: $RBoxKFour(1, ell)$,
      $Box (B^Vis -> C^Vis) seq(ell) Box Box (B^Vis -> C^Vis)$,
      noted(
        [(@lem:GentzenS_original_axioms, $RWk(1, 1)$)],
        $Box (B^Vis -> C^Vis), B^Vis -> C^Vis seq(1) Box (B^Vis -> C^Vis)$,
      ),
    ))
  $
]

#lemma[cf. @YS17[Lemma 5]][
  The following rule is admissible in $GentzenD$.
  $
    #prooftree(rule($Sigma^Vis, Box Gamma seq(ell) Box A$, $Sigma^Vis, Gamma, Box A seq(1) A$))
  $
] <lem:embedding_SPL_to_S_aux2>

#proof[
  First, we obtain $Box Sigma^Vis, Box Gamma seq(1) Box A$ as follows.
  $
    #prooftree(rule(
      name: $RBoxGL(1, 1)$,
      $Box Sigma^Vis, Box Gamma seq(1) Box A$,
      rule(
        name: $RWk(1, 1)$,
        $Box Sigma^Vis, Sigma^Vis, Box Gamma, Gamma, Box A seq(1) A$,
        $Sigma^Vis, Gamma, Box A seq(1) A$,
      ),
    ))
  $
  Now, by @lem:embedding_SPL_to_S_aux1, for every $B in Sigma$ we have $GentzenD proves B^Vis seq(1) Box B^Vis$.
  Hence, by applying $RCut(1, 1)$ an appropriate number of times to successively replace the elements of $Box Sigma^Vis$, we obtain $Sigma^Vis, Box Gamma seq(1) Box A$.
  When $ell = 2, 3$, we further apply $RLift(1, 2), RLift(2, 3)$.
]

#lemma[
  For every $p in PropVar$, $GentzenD proves Box p seq(2) p^Vis$.
] <lem:GD_box_to_Vis>

#proof[
  Follows from:
  $
    #prooftree(rule(
      name: $RAndR(2, 2)$,
      $Box p seq(2) p and Box p$,
      rule(name: $RBoxL(2, 2)$, $Box p seq(2) p$, rule(name: $RAx(2)$, $p seq(2) p$)),
      noted([(@lem:embedding_SPL_to_S_aux1)], $Box p seq(2) Box p$),
    ))
  $
]

#lemma[
  For every $p in PropVar$, $GentzenD proves p^Vis seq(3) Box p$.
] <lem:GD_Vis_to_box>

#proof[
  Follows from:
  $
    #prooftree(rule(
      name: $RAndL(3, 3)$,
      $p and Box p seq(3) Box p$,
      rule(
        name: $RWL(3, 3)$,
        $p, Box p seq(3) Box p$,
        noted([(@lem:embedding_SPL_to_S_aux1)], $Box p seq(3) Box p$),
      ),
    ))
  $
]

Thefore, we can prove half direction of @thm:embedding_GentzenSPL_GentzenS.

#lemma[cf. @Pet23[Lemma 4]][
  If $GentzenDPL proves Gamma seq(ell) Delta$, then $GentzenD proves Gamma^Vis seq(ell) Delta^Vis$ for $level = 1, 2, 3$. 
] <lem:embedding_SPL_to_S>

#proof[
  Proved by induction on the derivation.
  We show only the cases of $RImpR(1, 1)$, $RImpL(2, 2)$, $RLift(2, 3)$.

  *Case* $RImpR(1, 1)$:
  Fix $k$, and suppose the rule we now wish to consider has the following form.
  $
    #prooftree(rule(
      name: $RImpR(1, 1)$,
      $GentzenDPL proves Sigma, {C_j -> D_j : 0 <= j < k} seq(1) A -> B$,
      $GentzenDPL proves Delta_i, Sigma, A -> B, A seq(1) B, Gamma_i : 0 <= i < 2^k$,
    ))
  $
  By using the induction hypothesis for every $i$ with $0 <= i < 2^k$ we have $GentzenD proves Delta_i^Vis, Sigma^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis, Gamma_i^Vis$.
  Combining these sequents with $2^k - 1$ appropriate applications of $RImpL(1, 1)$, we obtain
  $GentzenD proves Sigma^Vis, {C_j^Vis -> D_j^Vis : 0 <= j < k}, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$.
  
  Here we illustrate the case $k = 2$ below; the construction is easy to generalize to arbitrary $k$.
  Let $cal(D)_1$ and $cal(D)_2$ be the following derivations.
  $
    #prooftree(rule(
      name: $RImpL(1, 1)$,
      $Sigma^Vis, C_0^Vis -> D_0^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis, C_1^Vis$,
      $Sigma^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis, C_0^Vis, C_1^Vis$,
      $D_0^Vis, Sigma^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis, C_1^Vis$,
    ))
  $
  $
    #prooftree(rule(
      name: $RImpL(1, 1)$,
      $D_1^Vis, Sigma^Vis, C_0^Vis -> D_0^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$,
      $D_1^Vis, Sigma^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis, C_0^Vis$,
      $D_0^Vis, D_1^Vis, Sigma^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$,
    ))
  $
  Then, applying $RImpL(1, 1)$ once more to the end sequents of $cal(D)_1$ and $cal(D)_2$, we obtain the desired sequent.
  $
    #prooftree(rule(
      name: $RImpL(1, 1)$,
      $Sigma^Vis, C_0^Vis -> D_0^Vis, C_1^Vis -> D_1^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$,
      subtree($cal(D)_1$, $Sigma^Vis, C_0^Vis -> D_0^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis, C_1^Vis$),
      subtree($cal(D)_2$, $D_1^Vis, Sigma^Vis, C_0^Vis -> D_0^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$),
    ))
  $

Finally, once obtained $GentzenD proves Sigma^Vis, {C_j^Vis -> D_j^Vis : 0 <= j < k}, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$, the rest can be carried out as follows:
  $
    #prooftree(rule(
      name: [@lem:embedding_SPL_to_S_aux2],
      $Sigma^Vis, {Box (C_j^Vis -> D_j^Vis) : 0 <= j < k} seq(1) Box (A^Vis -> B^Vis)$,
      rule(
        name: $RImpR(1, 1)$,
        $Sigma^Vis, {C_j^Vis -> D_j^Vis : 0 <= j < k}, Box (A^Vis -> B^Vis) seq(1) A^Vis -> B^Vis$,
        $Sigma^Vis, {C_j^Vis -> D_j^Vis : 0 <= j < k}, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$,
      ),
    ))
  $
  This is nothing but $GentzenD proves Sigma^Vis, {C_j -> D_j : 0 <= j < k}^Vis seq(1) (A -> B)^Vis$.

  *Case* $RImpL(2, 2)$:
  Suppose the rule we now wish to consider has the following form.
  $
    #prooftree(rule(
      name: $RImpL(2, 2)$,
      $GentzenDPL proves A -> B, Gamma seq(2) Delta$,
      $GentzenDPL proves  Gamma seq(2) Delta, A$,
      $GentzenDPL proves  B, Gamma seq(2) Delta$,
    ))
  $
  Then, by the induction hypothesis, we have $GentzenD proves Gamma^Vis seq(2) Delta^Vis, A^Vis$ and $GentzenD proves B^Vis, Gamma^Vis seq(2) Delta^Vis$.
  Given this, we proceed as follows.
  $
    #prooftree(rule(
      name: $RBoxL(2, 2)$,
      $Box (A^Vis -> B^Vis), Gamma^Vis seq(2) Delta^Vis$,
      rule(
        name: $RImpL(2, 2)$,
        $A^Vis -> B^Vis, Gamma^Vis seq(2) Delta^Vis$,
        $Gamma^Vis seq(2) Delta^Vis, A^Vis$,
        $B^Vis, Gamma^Vis seq(2) Delta^Vis$,
      ),
    ))
  $
  This is nothing but $GentzenD proves (A -> B)^Vis, Gamma^Vis seq(2) Delta^Vis$.

  *Case* $RLift(2, 3)$:
  Suppose the rule we now wish to consider has the following form, where $Phi$ is a set of propositional variables.
  $
    #prooftree(rule(
      name: $RLift(2, 3)$,
      $GentzenDPL proves {A_i -> B_i : 0 <= i < n}, Phi seq(3) {C_j -> D_j : 0 <= j < m}$,
      $GentzenDPL proves {A_i -> B_i : 0 <= i < n}, Phi seq(2) {C_j -> D_j : 0 <= j < m}$,
    ))
  $
  By the induction hypothesis, we have $GentzenD proves {Box(A^Vis_i -> B^Vis_i) : 0 <= i < n}, Phi^Vis seq(2) {Box(C^Vis_j -> D^Vis_j) : 0 <= j < m}$.
  Here every formula on both sides other than $Phi^Vis$ is boxed, but the formulas $p^Vis equiv p and Box p$ for $p in Phi$ are not, so the rule $RLift(2, 3)$ is not applicable yet.
  First, using @lem:GD_box_to_Vis and $RCut(2, 2)$ with the cut formula $p^Vis$, we successively replace each $p^Vis$ in the antecedent by $Box p$, and obtain
  $
    GentzenD proves {Box(A^Vis_i -> B^Vis_i) : 0 <= i < n}, Box Phi seq(2) {Box(C^Vis_j -> D^Vis_j) : 0 <= j < m}.
  $
  Since every formula in this sequent is boxed, the rule $RLift(2, 3)$ of $GentzenD$ applies and yields
  $
    GentzenD proves {Box(A^Vis_i -> B^Vis_i) : 0 <= i < n}, Box Phi seq(3) {Box(C^Vis_j -> D^Vis_j) : 0 <= j < m}.
  $
  Finally, using @lem:GD_Vis_to_box and $RCut(3, 3)$ with the cut formula $Box p$, we successively replace each $Box p$ back by $p^Vis$, and obtain
  $
    GentzenD proves {Box(A^Vis_i -> B^Vis_i) : 0 <= i < n}, Phi^Vis seq(3) {Box(C^Vis_j -> D^Vis_j) : 0 <= j < m},
  $
  which is nothing but $GentzenD proves {A_i -> B_i : 0 <= i < n}^Vis, Phi^Vis seq(3) {C_j -> D_j : 0 <= j < m}^Vis$.
]

Next, we prove the converse direction in the following strengthened form following the strategy of @YS17[Lemma 7].
Before proving, we defined the height of derivation with some modification.

#definition[
$GentzenD$ について，証明図 $cal(D)$ の*高さ* は，各leafまでに用いた *$RWk(level, level)$ 以外の* 規則の適用回数によって定めることとする．
シークエント $Gamma seq(level) Delta$ がこの意味の高さで高々 $h$ 以下の証明図で証明できるとき，$GentzenD attach(proves, tr: h) Gamma seq(level) Delta$ と書く．
]
つまりこの定義に基づくなら，$Gamma subset.eq Gamma', Delta subset.eq Delta'$ かつ $GentzenD attach(proves, tr: h) Gamma seq(level) Delta$ なら $GentzenD attach(proves, tr: h) Gamma' seq(level) Delta'$ を言うことが可能である．
さて，この意味の高さで，高さを保った反転補題などが成立することを示そう．

#lemma[Inversion rules $Inv(RImpL(ell, ell))$ of $GentzenD$][
  In $GentzenD$ the inversion rules $Inv(RImpL(ell, ell))$ are height-preservingly admissible.
  That is, for every $h$, if $A -> B in.not Gamma$ then the following hold.
  #side-by-side(
    prooftree(rule(
      name: $Inv(RImpL(ell, ell))$,
      $GentzenD provesh(h) Gamma seq(ell) Delta, A$,
      $GentzenD provesh(h) A -> B, Gamma seq(ell) Delta$,
    )),
    prooftree(rule(
      name: $Inv(RImpL(ell, ell))$,
      $GentzenD provesh(h) B, Gamma seq(ell) Delta$,
      $GentzenD provesh(h) A -> B, Gamma seq(ell) Delta$,
    )),
  )
  We call the two conclusions the _left_ and the _right_ one.
] <lem:GentzenD_inversion_ImpL>

#proof[
  We show the following by induction on a derivation $cal(D)$ of $Gamma seq(ell) Delta$ with $A -> B in Gamma$:
  there are derivations of $Gamma without {A -> B} seq(ell) Delta, A$ and of $B, Gamma without {A -> B} seq(ell) Delta$ whose heights are at mos the height of $cal(D)$.
  We distinguish cases by the last rule of $cal(D)$.
  We display only those for the left conculusion.

  *Case $RAx(ell)$, $RBotL(ell)$, $RBoxGL(1, 1)$, $RLift(2, 3)$:*
  The antecedent of the conclusion consists only of propositional variables, $bot$ and formulas of the form $Box C$, so it does not contain $A -> B$.
  Thus this case does not occur.

  *Case $RWk(ell, ell)$:*
  The last rule is of the form below, where $Gamma_0 subset.eq Gamma$ and $Delta_0 subset.eq Delta$; and the premise also has height at most $h$.
  $
    #prooftree(rule(name: $RWk(ell, ell)$, $GentzenD provesh(h) Gamma seq(ell) Delta$, $GentzenD provesh(h) Gamma_0 seq(ell) Delta_0$))
  $
  If $A -> B in Gamma_0$, we use the left derivation below; otherwise $Gamma_0 subset.eq Gamma without {A -> B}$, and we use the right one:
  #side-by-side(
    prooftree(rule(
      name: $RWk(ell, ell)$,
      $GentzenD provesh(h) Gamma without {A -> B} seq(ell) Delta, A$,
      ih($GentzenD provesh(h) Gamma_0 without {A -> B} seq(ell) Delta_0, A$),
    )),
    prooftree(rule(
      name: $RWk(ell, ell)$,
      $GentzenD provesh(h) Gamma without {A -> B} seq(ell) Delta, A$,
      $GentzenD provesh(h) Gamma_0 seq(ell) Delta_0$,
    )),
  )

  *Case $RImpL(ell, ell)$:*
  The last rule is of the form below, where $Gamma = Gamma' union {C -> D}$.
  $
    #prooftree(rule(
      name: $RImpL(ell, ell)$,
      $GentzenD provesh(h) C -> D, Gamma' seq(ell) Delta$,
      $GentzenD provesh(h-1) Gamma' seq(ell) Delta, C$,
      $GentzenD provesh(h-1) D, Gamma' seq(ell) Delta$,
    ))
  $
  - Suppose $C -> D equiv A -> B$.
    - If $A -> B in.not Gamma'$, then $Gamma' = Gamma without {A -> B}$, and the two premises $GentzenD provesh(h-1) Gamma without {A -> B} seq(ell) Delta, A$ and $GentzenD provesh(h-1) B, Gamma without {A -> B} seq(ell) Delta$ are the desired sequents.
    - If $A -> B in Gamma'$, we apply the induction hypothesis for the left conclusion to the left premise, and that for the right conclusion to the right premise, and obtain the same two sequents.
  - Suppose $C -> D equiv.not A -> B$ and $D equiv.not A -> B$.
    Then $A -> B in Gamma'$ and $Gamma without {A -> B} = (Gamma' without {A -> B}) union {C -> D}$.
    We can show by below derivation:
    $
      #prooftree(rule(
        name: $RImpL(ell, ell)$,
        $GentzenD provesh(h) C -> D, Gamma' without {A -> B} seq(ell) Delta, A$,
        ih($GentzenD provesh(h-1) Gamma' without {A -> B} seq(ell) Delta, C, A$),
        ih($GentzenD provesh(h-1) D, Gamma' without {A -> B} seq(ell) Delta, A$),
      ))
    $
  - Suppose $C -> D equiv.not A -> B$ and $D equiv A -> B$.
    Applying the induction hypothesis to the right premise removes $D$ as well, so we add $C -> D$ by weakening.
    $
      #prooftree(rule(
        name: $RWk(ell, ell)$,
        $GentzenD provesh(h-1) C -> D, Gamma' without {A -> B} seq(ell) Delta, A$,
        ih($GentzenD provesh(h-1) Gamma' without {A -> B} seq(ell) Delta, A$),
      ))
    $

  *Case $RImpR(ell, ell)$:*
  The last rule is of the form below, where $Delta = Delta' union {C -> D}$.
  $
    #prooftree(rule(name: $RImpR(ell, ell)$, $GentzenD provesh(h) Gamma seq(ell) Delta', C -> D$, $GentzenD provesh(h-1) C, Gamma seq(ell) Delta', D$))
  $
  - If $C equiv.not A -> B$, use the derivation below.
    $
    #prooftree(rule(
      name: $RImpR(ell, ell)$,
      $GentzenD provesh(h) Gamma without {A -> B} seq(ell) Delta', C -> D, A$,
      ih($GentzenD provesh(h-1) C, Gamma without {A -> B} seq(ell) Delta', D, A$),
    ))
    $
  - If $C equiv A -> B$, the induction hypothesis removes $C$ as well, so add it back by weakening before applying $RImpR(ell, ell)$, and use the below derivation.
    $
      #prooftree(rule(
        name: $RImpR(ell, ell)$,
        $GentzenD provesh(h) Gamma without {A -> B} seq(ell) Delta', (A -> B) -> D, A$,
        rule(
          name: $RWk(ell, ell)$,
          $GentzenD provesh(h-1) A -> B, Gamma without {A -> B} seq(ell) Delta', D, A$,
          ih($GentzenD provesh(h-1) Gamma without {A -> B} seq(ell) Delta', D, A$),
        ),
      ))
    $

  *Case $RBoxL(2, 2)$:*
  The last rule is of the form below, where $Gamma = Gamma' union {Box C}$; since $Box C equiv.not A -> B$, we have $A -> B in Gamma'$.
  $
    #prooftree(rule(name: $RBoxL(2, 2)$, $GentzenD provesh(h) Box C, Gamma' seq(2) Delta$, $GentzenD provesh(h-1) C, Gamma' seq(2) Delta$))
  $
  - If $C equiv.not A -> B$, use the derivation below:
    $
    #prooftree(rule(
      name: $RBoxL(2, 2)$,
      $GentzenD provesh(h) Box C, Gamma' without {A -> B} seq(2) Delta, A$,
      ih($GentzenD provesh(h-1) C, Gamma' without {A -> B} seq(2) Delta, A$),
    ))
    $
  - If $C equiv A -> B$, use the derivation below:
    $
    #prooftree(rule(
      name: $RWk(2, 2)$,
      $GentzenD provesh(h-1) Box C, Gamma' without {A -> B} seq(2) Delta, A$,
      ih($GentzenD provesh(h-1) Gamma' without {A -> B} seq(2) Delta, A$),
    ))
 $

  *Case $RLift(1, 2)$:*
  We apply the induction hypothesis to the premise and then $RLift(1, 2)$.
  $
    #prooftree(rule(
      name: $RLift(1, 2)$,
      $GentzenD provesh(h) Gamma without {A -> B} seq(2) Delta, A$,
      ih($GentzenD provesh(h-1) Gamma without {A -> B} seq(1) Delta, A$),
    ))
  $

  For the right conclusion, use similar construction to left one.
]

#lemma[Inversion rule $Inv(RImpR(ell, ell))$ of $GentzenD$][
  In $GentzenD$ the inversion rule $Inv(RImpR(ell, ell))$ is height-preservingly admissible.
  That is, for every $h$, if $A -> B in.not Delta$ then the following holds.
  $
    #prooftree(rule(
      name: $Inv(RImpR(ell, ell))$,
      $GentzenD provesh(h) A, Gamma seq(ell) Delta, B$,
      $GentzenD provesh(h) Gamma seq(ell) Delta, A -> B$,
    ))
  $
] <lem:GentzenD_inversion_ImpR>

#proof[
  We show the following by induction on a derivation $cal(D)$ of $Gamma seq(ell) Delta$ with $A -> B in Delta$:
  there is a derivation of $A, Gamma seq(ell) Delta without {A -> B}, B$ whose height is at most $h(cal(D))$.
  Since $A -> B in.not Delta$ in the statement, the lemma follows.
  Let $h := h(cal(D))$; we distinguish cases by the last rule of $cal(D)$, with the same conventions as in the proof of @lem:GentzenD_inversion_ImpL.

  *Case $RAx(ell)$, $RBotL(ell)$, $RBoxGL(1, 1)$, $RLift(2, 3)$:*
  The succedent of the conclusion consists only of propositional variables and formulas of the form $Box C$, so it does not contain $A -> B$.
  Thus this case does not occur.

  *Case $RWk(ell, ell)$:*
  The last rule is of the form below, where $Gamma_0 subset.eq Gamma$ and $Delta_0 subset.eq Delta$; the premise also has height at most $h$.
  $
    #prooftree(rule(name: $RWk(ell, ell)$, $GentzenD provesh(h) Gamma seq(ell) Delta$, $GentzenD provesh(h) Gamma_0 seq(ell) Delta_0$))
  $
  If $A -> B in Delta_0$, we use the left derivation below; otherwise $Delta_0 subset.eq Delta without {A -> B}$, and we use the right one.
  #side-by-side(
    prooftree(rule(
      name: $RWk(ell, ell)$,
      $GentzenD provesh(h) A, Gamma seq(ell) Delta without {A -> B}, B$,
      ih($GentzenD provesh(h) A, Gamma_0 seq(ell) Delta_0 without {A -> B}, B$),
    )),
    prooftree(rule(
      name: $RWk(ell, ell)$,
      $GentzenD provesh(h) A, Gamma seq(ell) Delta without {A -> B}, B$,
      $GentzenD provesh(h) Gamma_0 seq(ell) Delta_0$,
    )),
  )

  *Case $RImpL(ell, ell)$:*
  The last rule is of the form below.
  $
    #prooftree(rule(
      name: $RImpL(ell, ell)$,
      $GentzenD provesh(h) C -> D, Gamma' seq(ell) Delta$,
      $GentzenD provesh(h-1) Gamma' seq(ell) Delta, C$,
      $GentzenD provesh(h-1) D, Gamma' seq(ell) Delta$,
    ))
  $
  If $C equiv.not A -> B$, we use the first derivation below.
  If $C equiv A -> B$, the induction hypothesis applied to the left premise removes $C$ as well, and we use the second derivation.
  #wide(prooftree(rule(
    name: $RImpL(ell, ell)$,
    $GentzenD provesh(h) A, C -> D, Gamma' seq(ell) Delta without {A -> B}, B$,
    ih($GentzenD provesh(h-1) A, Gamma' seq(ell) Delta without {A -> B}, C, B$),
    ih($GentzenD provesh(h-1) A, D, Gamma' seq(ell) Delta without {A -> B}, B$),
  )))
  $
    #prooftree(rule(
      name: $RWk(ell, ell)$,
      $GentzenD provesh(h-1) A, C -> D, Gamma' seq(ell) Delta without {A -> B}, B$,
      ih($GentzenD provesh(h-1) A, Gamma' seq(ell) Delta without {A -> B}, B$),
    ))
  $

  *Case $RImpR(ell, ell)$:*
  The last rule is of the form below, where $Delta = Delta' union {C -> D}$.
  $
    #prooftree(rule(name: $RImpR(ell, ell)$, $GentzenD provesh(h) Gamma seq(ell) Delta', C -> D$, $GentzenD provesh(h-1) C, Gamma seq(ell) Delta', D$))
  $
  - Suppose $C -> D equiv A -> B$.
    If $A -> B in.not Delta'$, then $Delta' = Delta without {A -> B}$, and the premise $GentzenD provesh(h-1) A, Gamma seq(ell) Delta without {A -> B}, B$ is the desired sequent.
    If $A -> B in Delta'$, we apply the induction hypothesis to the premise and obtain the same sequent; note that $B equiv.not A -> B$.
  - Suppose $C -> D equiv.not A -> B$ and $D equiv.not A -> B$.
    Then $A -> B in Delta'$ and $Delta without {A -> B} = (Delta' without {A -> B}) union {C -> D}$.
    $
      #prooftree(rule(
        name: $RImpR(ell, ell)$,
        $GentzenD provesh(h) A, Gamma seq(ell) Delta' without {A -> B}, C -> D, B$,
        ih($GentzenD provesh(h-1) A, C, Gamma seq(ell) Delta' without {A -> B}, D, B$),
      ))
    $
  - Suppose $C -> D equiv.not A -> B$ and $D equiv A -> B$.
    The induction hypothesis removes $D$ as well, so we add it back by weakening before applying $RImpR(ell, ell)$.
    $
      #prooftree(rule(
        name: $RImpR(ell, ell)$,
        $GentzenD provesh(h) A, Gamma seq(ell) Delta' without {A -> B}, C -> (A -> B), B$,
        rule(
          name: $RWk(ell, ell)$,
          $GentzenD provesh(h-1) A, C, Gamma seq(ell) Delta' without {A -> B}, A -> B, B$,
          ih($GentzenD provesh(h-1) A, C, Gamma seq(ell) Delta' without {A -> B}, B$),
        ),
      ))
    $

  *Case $RBoxL(2, 2)$, $RLift(1, 2)$:*
  We apply the induction hypothesis to the premise and then the same rule.
  #side-by-side(
    prooftree(rule(
      name: $RBoxL(2, 2)$,
      $GentzenD provesh(h) A, Box C, Gamma' seq(2) Delta without {A -> B}, B$,
      ih($GentzenD provesh(h-1) A, C, Gamma' seq(2) Delta without {A -> B}, B$),
    )),
    prooftree(rule(
      name: $RLift(1, 2)$,
      $GentzenD provesh(h) A, Gamma seq(2) Delta without {A -> B}, B$,
      ih($GentzenD provesh(h-1) A, Gamma seq(1) Delta without {A -> B}, B$),
    )),
  )
]

#lemma[cf. @Pet23[Lemma 5]][
  Let $Gamma, Delta$ be sets of propositional formulas and let $Phi_1, Phi_2, Psi$ be sets of propositional variables.
  If $GentzenD proves Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, Delta^Vis$,
  then $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(ell) Psi, Delta$.
] <lem:embedding_S_to_SPL_general>

#proof[
  First, observe that every formula occurring in the assumed sequent is of exactly one of the following forms:
  a translation $A^Vis$, which is either $bot$ or has $and$, $or$ or $Box$ as its outermost connective;
  a propositional variable; or a boxed propositional variable.
  In particular, no formula in the sequent is an implication,
  and hence the last rule of a derivation of the assumed sequent is neither $RImpL(ell, ell)$ nor $RImpR(ell, ell)$.
  With this in mind, we prove the claim by induction on the height of the derivation,
  distinguishing cases according to the last rule and the position of its principal formula.

  Note that the statement is generalized over $Gamma, Delta, Phi_1, Phi_2$ and $Psi$:
  in each case below, the premise of the last rule is re-decomposed into the form $Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, Delta^Vis$, possibly with components different from those of the conclusion, and the induction hypothesis is applied to this decomposition.
  We illustrate this point concretely in the case $RAndL(ell, ell)$ below.

  *Case* $RAx(ell)$:
  The sequent is $p seq(ell) p$, that is, $Gamma = Delta = Phi_2 = emptyset$ and $Phi_1 = Psi = {p}$.
  The rule $RAx(ell)$ of $GentzenDPL$ yields the desired $GentzenDPL proves p seq(ell) p$.

  *Case* $RBotL(ell)$:
  The sequent is $bot seq(ell)$, that is, $Gamma = {bot}$ and all the other components are empty.
  The rule $RBotL(ell)$ of $GentzenDPL$ yields the desired sequent.

  *Case* $RWk(ell, ell)$, $RLift(1, 2)$:
  These follow straightforwardly from the induction hypothesis and the corresponding rule of $GentzenDPL$.
  We only note that no weakening is needed in $GentzenDPL$ when $RWk(ell, ell)$ introduces a variable $p in Phi_1$ with $p in Phi_2$, or a boxed variable $Box p$ with $p in Phi_1$:
  in these cases the antecedent of the sequent given by the induction hypothesis already coincides with $Gamma, Phi_1, Phi_2$ as a set.
 
  *Case* $RBoxGL(1, 1)$:
  Since the antecedent of the conclusion of an application of $RBoxGL(1, 1)$ consists of boxed formulas only and its succedent consists of exactly one boxed formula,
  we have $Phi_1 = Psi = emptyset$, $Gamma = {C_j -> D_j : 0 <= j < k}$ for some $k >= 0$ and formulas $C_j, D_j$ ($0 <= j < k$), and $Delta = {E -> F}$ for some formulas $E, F$.
  The application we are concerned with is thus the following.
  $
    #prooftree(rule(
      name: $RBoxGL(1, 1)$,
      $GentzenD provesh(h) Box{C^Vis_j -> D^Vis_j : 0 <= j < k}, Box Phi_2 seq(1) Box(E^Vis -> F^Vis)$,
      $GentzenD provesh(h-1) {C^Vis_j -> D^Vis_j : 0 <= j < k}, Phi_2, Box{C^Vis_j -> D^Vis_j : 0 <= j < k}, Box Phi_2, Box(E^Vis -> F^Vis) seq(1) E^Vis -> F^Vis$,
    ))
  $
  Applying the height-preserving inversion $Inv(RImpR(1, 1))$ (@lem:GentzenD_inversion_ImpR) to the premise, we obtain the following.
  $
    GentzenS provesh(h-1) {C^Vis_j -> D^Vis_j : 0 <= j < k}, Phi_2, Box{C^Vis_j -> D^Vis_j : 0 <= j < k}, Box Phi_2, Box(E^Vis -> F^Vis), E^Vis seq(1) F^Vis.
  $
  Furthermore, the height-preserving inversion $Inv(RImpL(1, 1))$ (@lem:GentzenD_inversion_ImpL) applies to the members of ${C^Vis_j -> D^Vis_j : 0 <= j < k}$, so, following the definition of $RImpR(1, 1)$ in $GentzenDPL$ and determining $Gamma_i, Delta_i$ from $C_0, dots, C_(k-1)$ and $D_0, dots, D_(k-1)$, for each $i$ with $0 <= i < 2^k$ we obtain the following.
  $
    GentzenS provesh(h-1) Delta^Vis_i, Phi_2, Box{C^Vis_j -> D^Vis_j : 0 <= j < k}, Box Phi_2, Box(E^Vis -> F^Vis), E^Vis seq(1) F^Vis, Gamma^Vis_i.
  $
  Each of these sequents is again of the form required in the statement:
  since $Box{C^Vis_j -> D^Vis_j : 0 <= j < k} = {C_j -> D_j : 0 <= j < k}^Vis$ and $Box(E^Vis -> F^Vis) = (E -> F)^Vis$,
  its antecedent consists of the translations of $Delta_i, {C_j -> D_j : 0 <= j < k}, E -> F, E$, the variables $Phi_2$, and the boxed variables $Box Phi_2$.
  Since the height is $h - 1$, the induction hypothesis applies and yields the following.
  $
    GentzenDPL proves Delta_i, {C_j -> D_j : 0 <= j < k}, E -> F, E, Phi_2 seq(1) F, Gamma_i.
  $
  Applying $RImpR(1, 1)$ of $GentzenDPL$ with $Sigma := {C_j -> D_j : 0 <= j < k} union Phi_2$ to these premises, we obtain the following, where we note that antecedents are sets and hence the duplicated occurrences of $C_j -> D_j$ are contracted.
  $
    GentzenDPL proves {C_j -> D_j : 0 <= j < k}, Phi_2 seq(1) E -> F.
  $
  This is the desired sequent $Gamma, Phi_1, Phi_2 seq(1) Psi, Delta$.
  
  *Case* $RBoxL(2, 2)$:
  The principal formula is either $Box p$ for some $p in Phi_2$, or $(E -> F)^Vis = Box(E^Vis -> F^Vis)$ for some $E -> F in Gamma$.

  In the former case, the application we are concerned with is the following.
  $
    #prooftree(rule(
      name: $RBoxL(2, 2)$,
      $GentzenD provesh(h) Box p, Gamma^Vis, Phi_1, Box(Phi_2 without {p}) seq(2) Psi, Delta^Vis$,
      $GentzenD provesh(h-1) p, Gamma^Vis, Phi_1, Box(Phi_2 without {p}) seq(2) Psi, Delta^Vis$,
    ))
  $
  The induction hypothesis applied to the premise, with the components $Phi_1 union {p}$ and $Phi_2 without {p}$, yields
  $GentzenDPL proves Gamma, Phi_1, p, Phi_2 without {p} seq(2) Psi, Delta$,
  whose antecedent coincides with $Gamma, Phi_1, Phi_2$ as a set, since $p in Phi_2$.

  In the latter case, the application we are concerned with is the following.
  $
    #prooftree(rule(
      name: $RBoxL(2, 2)$,
      $GentzenD provesh(h) Box(E^Vis -> F^Vis), (Gamma without {E -> F})^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
      $GentzenD provesh(h-1) E^Vis -> F^Vis, (Gamma without {E -> F})^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
    ))
  $
  Applying the height-preserving inversion $Inv(RImpL(2, 2))$ (@lem:GentzenD_inversion_ImpL) to the premise, we obtain the following.
  $
    GentzenD & provesh(h-1) (Gamma without {E -> F})^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis, E^Vis \
    GentzenD & provesh(h-1) F^Vis, (Gamma without {E -> F})^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis.
  $
  Since the height is $h - 1$, the induction hypothesis applies and yields the following.
  $
    GentzenDPL & proves (Gamma without {E -> F}), Phi_1, Phi_2 seq(2) Psi, Delta, E \
    GentzenDPL & proves F, (Gamma without {E -> F}), Phi_1, Phi_2 seq(2) Psi, Delta.
  $
  Using $RImpL(2, 2)$ we obtain $GentzenDPL proves E -> F, (Gamma without {E -> F}), Phi_1, Phi_2 seq(2) Psi, Delta$, that is, $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(2) Psi, Delta$.

  *Case* $RLift(2, 3)$:
  We have $Phi_1 = Psi = emptyset$ since every formula in the conclusion of an application of $RLift(2, 3)$ of $GentzenD$ is boxed.
  Moreover, since the boxed formulas among the translations are exactly those of implications,
  we have $Gamma = {A_i -> B_i : 0 <= i < n}$ and $Delta = {C_j -> D_j : 0 <= j < m}$ for some $n, m >= 0$ and formulas $A_i, B_i$ ($0 <= i < n$), $C_j, D_j$ ($0 <= j < m$).
  Thus, the application we are concerned with is the following.
  $
    #prooftree(rule(
      name: $RLift(2, 3)$,
      $GentzenD provesh(h) {A_i -> B_i : 0 <= i < n}^Vis, Box Phi_2 seq(3) {C_j -> D_j : 0 <= j < m}^Vis$,
      $GentzenD provesh(h-1) {A_i -> B_i : 0 <= i < n}^Vis, Box Phi_2 seq(2) {C_j -> D_j : 0 <= j < m}^Vis$,
    ))
  $
  The induction hypothesis applied to the premise yields $GentzenDPL proves {A_i -> B_i : 0 <= i < n}, Phi_2 seq(2) {C_j -> D_j : 0 <= j < m}$.
  Since ${A_i -> B_i : 0 <= i < n}$ and ${C_j -> D_j : 0 <= j < m}$ consist of implications and $Phi_2$ consists of propositional variables,
  the rule $RLift(2, 3)$ of $GentzenDPL$ applies and yields
  $GentzenDPL proves {A_i -> B_i : 0 <= i < n}, Phi_2 seq(3) {C_j -> D_j : 0 <= j < m}$,
  which is the desired sequent since $Phi_1 = emptyset$.
]
 
#theorem[cf. @Pet23[Theorem 1]][
  $GentzenDPL proves Gamma seq(ell) Delta$ iff $GentzenD proves Gamma^Vis seq(ell) Delta^Vis$.
] <thm:embedding_GentzenSPL_GentzenS>

#proof[
  Combining @lem:embedding_SPL_to_S and @lem:embedding_S_to_SPL_general with taking $Phi_1 = Phi_2 = Psi = emptyset$.
]

Combining @prop:GentzenS_provability and @prop:GentzenS_cut_elimination with this theorem, we immediately obtain the following corollaries.

#corollary[
  Let $A in FmlPL$.

  + $LogicFPL proves A <==> GentzenDPL proves emptyset seq(1) {A} <==> LogicGL proves A^Vis$
  + $LogicSPL proves A <==> GentzenDPL proves emptyset seq(2) {A} <==> LogicS proves A^Vis$
  + $LogicDPL proves A <==> GentzenDPL proves emptyset seq(3) {A} <==> LogicD proves A^Vis$
]

#corollary[Cut-admissibility of $GentzenDPL$][
  the cut rule $RCut(level, level)$ is admissible in $GentzenDPL$.
]

@YS17 ではやられていなかった $LogicFPL$--$LogicGL$ 間の構文論的な埋め込みについても，これらの体系および証明を適当に $level = 1$ のものに制限すれば行える，ということは注意しておく．

== Errors in Petrukhin's proof <sect:errors_in_Petrukhin>

This embedding result is based on Petrukhin @Pet23, but the proof in the original paper appears to contain several errors.
We point them out below.
The issue concerns @Pet23[Lemma 5], which corresponds to @lem:embedding_S_to_SPL_general in the present paper.

#proposition(numbering: none)[@Pet23[Lemma 5]][
  If $GentzenS proves Gamma^Vis, Phi, Box Phi seq(ell) Psi, Delta^Vis$, then $GentzenSPL proves Gamma, Phi seq(ell) Psi, Delta$.
  Here $Gamma, Delta$ are multisets of formulas and $Phi, Psi$ are multisets of propositional variables.
]

The proof proceeds by induction on the height of the proof-tree of $GentzenS proves Gamma^Vis, Phi, Box Phi seq(ell) Psi, Delta^Vis$.
Petrukhin claims that the proof proceeds as in @YS17[Lemma 7], but the problem occurs in the case of $RBoxL(2, 2)$.
Petrukhin verifies only the case where the principal formula is $Box(E^Vis -> F^Vis)$.
To begin with, this verification itself is erroneous.
The proof-tree given there is the following (cf. @Pet23[p.~17]).
$
  #prooftree(rule(
    name: $RBoxL(2, 2)$,
    $GentzenS provesh(h) Box(E^Vis -> F^Vis), Gamma^Vis, Phi seq(2) Psi, Delta^Vis$,
    $GentzenS provesh(h-1) E^Vis -> F^Vis, Gamma^Vis, Phi seq(2) Psi, Delta^Vis$,
  ))
$
There are two problems.
First, $Box Phi$ is missing from both the conclusion and the premise.
Second, even if we supply it and regard the premise as $GentzenS provesh(h-1) E^Vis -> F^Vis, Gamma^Vis, Phi, Box Phi seq(2) Psi, Delta^Vis$, the induction hypothesis cannot be applied to this premise.
This is because $E^Vis -> F^Vis$ never belongs to $Sigma^Vis$ for any $Sigma$, and is of course not a propositional variable, so the premise is not of the form $Gamma^Vis, Phi, Box Phi seq(ell) Psi, Delta^Vis$.
Nevertheless, Petrukhin appears to apply the induction hypothesis to this premise and obtain $E -> F, Gamma, Phi seq(2) Psi, Delta$, which is not justified.

Furthermore, one should in fact also consider the case where, for some $p in Phi$, the principal formula is $Box p$.
In this case the proof-tree is as follows.
$
  #prooftree(rule(
    name: $RBoxL(2, 2)$,
    $GentzenS provesh(h) Box p, Gamma^Vis, p, Phi without {p}, Box(Phi without {p}) seq(2) Psi, Delta^Vis$,
    $GentzenS provesh(h-1) p, Gamma^Vis, p, (Phi without {p}), Box(Phi without {p}) seq(2) Psi, Delta^Vis$,
  ))
$
Now, in order to apply the induction hypothesis to this premise and carry the argument through, one would need to obtain, by _height-preserving_ weakening and contraction on the premise, $GentzenS provesh(h-1) p, Box p, Gamma^Vis, (Phi without {p}), Box(Phi without {p}) seq(2) Psi, Delta^Vis$.
However, such height-preserving weakening and contraction cannot be carried out in $GentzenS$#footnote[The calculus adopted by @Pet23 is the sequent calculus of @Kus20, but this does not affect the details of the argument.] (cf. @NvP11).
The reason this problem did not arise in the proof of @YS17 is that the sequent system for $LogicKFour$ adopted there is of G3-type (cf. @TS00).
In that system, the weakening, contraction, and inversion rules are height-preservingly admissible#footnote[However, @YS17 does not make explicit how these properties are established for their extension to $LogicKFour$.].

In this paper, these problems are avoided in @lem:embedding_S_to_SPL_general as follows.
Since our sequents are based on _sets_, contraction is built into the formulation and never needs to be applied explicitly, let alone height-preservingly.
Moreover, the problematic case where the principal formula of $RBoxL(2, 2)$ is $Box p$ is absorbed by allowing the two sets of variables $Phi_1$ and $Phi_2$ in the statement to differ:
unboxing $Box p$ merely moves $p$ from $Phi_2$ to $Phi_1$, so the induction hypothesis applies directly, without any use of weakening.


= Concluding Remarks and Open Problems <sect:conclusion>

In this paper, we examined the proof by Petrukhin @Pet23 of the embedding of the propositional logic $LogicSPL$ into Solovay's provability logic $LogicS$, and gave a correct proof.
Furthermore, extending that proof, we proposed a new propositional logic $LogicDPL$ by means of the sequent calculus for Japaridze's provability logic $LogicD$ introduced by Kashima et al.~@KKIM25, and proved the corresponding embedding as well.
In the rest of this section, we discuss some issues concerning $LogicSPL$ and $LogicDPL$ that were not addressed in this paper, together with directions for future work.

== Semantics

We did not discuss the properties that the logics $LogicSPL$ and $LogicDPL$ have in their own right.
For instance, $LogicFPL$ as a provability logic was already considered in Visser's original paper @Vis81.
Since $LogicSPL$ and $LogicDPL$ are the counterparts of $LogicS$ and $LogicD$ respectively,
it is natural to expect that this line of investigation makes sense for them as well.
Moreover, Petrukhin @Pet23 also examines natural deduction and semantics for $LogicSPL$.
In particular, as for semantics, he introduces a suitable counterpart of Visser's tail models @Vis84
on the propositional side and proves its completeness through the embedding.
From the perspective of Kripke semantics for propositional logics,
Visser's translation maps $p$ to $p and Box p$ precisely so that $Box p$ restores the persistency#footnote[For a Kripke model $chevron.l W, R, forces chevron.r$, if $x forces p$ and $x R y$ then $y forces p$.]
of Kripke models.
On the other hand, we believe that it should also be possible to define semantics for $LogicSPL$ directly
and to prove its completeness without going through the embedding, but so far we have not succeeded.
As for $LogicD$, semantics has been defined by Beklemishev @Bek89 @Bek90 and by Kashima et al.~@KKIM25.
Note that a discussion of the semantics of $LogicDPL$ via the embedding would be possible, but we did not present it here.

We consider the problem of semantics to be rather important, for the following somewhat subtle reason.
Suppose that there is a propositional logic that corresponds (or _should_ correspond) to $LogicS$ or $LogicD$.
Then, for practical purposes, we consider that the justification of the correspondence should be witnessed by
some semantics, such as Kripke-style or arithmetical interpretations.
In this paper, we defined the logics $LogicSPL$ and $LogicDPL$ by sequent calculi,
and we cannot eliminate the possibility that they are, in a sense, ad hoc systems built solely in order to claim the embeddability.
In other words, it is conceivable that different logics $LogicSPL'$ and $LogicDPL'$,
obtained by slightly modifying the definitions of $GentzenDPL$, can also be embedded into $LogicS$ and $LogicD$;
in such a case, one may ask what the difference between them really is, or object that they are _merely_ syntactically different.
If, on the other hand, the correspondence is matched precisely at the semantic level,
one could respond to such criticism with some substantial grounds.
For these reasons, we regard the semantic witnessing of $LogicSPL$ and $LogicDPL$ as a major problem for future work.

== Hilbert-style formulations

Hilbert-style systems for $LogicBPL$ and $LogicFPL$ have been studied in @SO97 @IKK01.
A natural question is then what Hilbert-style systems for $LogicSPL$ and $LogicDPL$ look like.
However, we defined $LogicSPL$ and $LogicDPL$ by sequent calculi, and moreover by sequent calculi with several levels of sequents.
Defining Hilbert-style systems seems to be far from easy.
In fact, we conjecture that no Hilbert-style system exists in the language with a single level of implication $->$.
If this conjecture is true, further questions arise:
what is a logic in a language equipped with several levels of implications $attach(->, tr: 1)$ and $attach(->, tr: 2)$,
and what do such implications mean?

== Syntactic cut-elimination

The embeddability and the cut-admissibility of our systems for $LogicSPL$ and $LogicDPL$ rely
on the cut-admissibility of the sequent calculi for $LogicS$ and $LogicD$,
and the latter is established by semantic arguments in @KKIM25, so our results are not purely syntactic.
It is still open to give a constructive cut-elimination algorithm for the sequent calculi $GentzenDPL$.
