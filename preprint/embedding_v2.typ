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
  $LogicGL subset LogicD subset LogicS$.
  That is, $LogicGL proves A$ implies $LogicD proves A$, and $LogicD proves A$ implies $LogicS proves A$, but the converses do not hold.
]

The Gödel translation is a wlev-known embedding of intuitionistic propositional logic into modal logic.

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


オリジナルのGödel変換とVisser--Gödel変換の間では $p$ と $bot$ の送り先は以下のように異なる：$p$ は $Box p$ へ送られる．$bot$ は $Box bot$ へ送られる．

#proposition[@Vis81][
  Let $A in FmlPL$. These following are equivalent.
  1. $LogicFPL proves A$. 
  2. $LogicGL proves A^Vis$.
  3. $LogicGL proves A^God$.
]

/*
Finally, we fix the proof-theoretic terminology used throughout this paper.
For the sequent calculi introduced in the following sections,
the notions of a proof-tree and its height, and of (height-preserving) admissible rules,
are defined as usual (see e.g. @TS00 @NvP11).
We write $sans(upright(G)) proves S$ if a sequent $S$ is derivable in a sequent calculus $sans(upright(G))$,
and $sans(upright(G)) provesh(h) S$ if $S$ is derivable in $sans(upright(G))$ by a proof-tree of height at most $h$.
For a formula $A$ and sets $Gamma, Delta$ of formulas, in the context of sequents,
we write $A, Gamma$ for ${A} union Gamma$ and $Gamma, Delta$ for $Gamma union Delta$.
Note that $A, Gamma = Gamma$ when $A in Gamma$, so that contraction is built into this notation.
*/

== Sequent calculus for provability logics

Although Kushida @Kus20 first introduced a sequent calculus for $LogicS$, his formulation is not suitable for our purpose.
我々は @KKIM25 の $LogicD$ のためのアプローチを少し修正して採用し，その部分体系として $LogicS$ のシークエント計算を導入する．
このセクションでは導入と，いくらかの証明論的な性質を述べておく．

#definition[
  Let $Gamma, Delta$ be sets of formulas and let $level = 1, 2, 3$.
  An expression of the form $Gamma seq(level) Delta$ is called a _sequent_.

  The sequent calculus $GentzenS$ for $LogicS$, in which sequents of level $level = 1, 2$ occur, is defined by the following rules.

  #side-by-side(
    align: center + top,
    [
      #prooftree(rule(name: $RAx(level)$, $p seq(level) p$))
      where $p in PropVar$.
    ],
    prooftree(rule(name: $RBotL(level)$, $bot seq(level)$)),
  )

  #side-by-side(
    prooftree(rule(name: $RWL(level, level)$, $Gamma' seq(level) Delta'$, $Gamma seq(level) Delta$)),
    prooftree(rule(name: $RWR(level, level)$, $Gamma seq(level) Delta, A$, $Gamma seq(level) Delta$)),
  )

  $
    #prooftree(rule(name: $RLift(1, 2)$, $Gamma seq(2) Delta$, $Gamma seq(1) Delta$))
  $ 

  #side-by-side(
    prooftree(rule(
      name: $RImpL(level, level)$,
      $A -> B, Gamma seq(level) Delta$,
      $Gamma seq(level) Delta, A$,
      $B, Gamma seq(level) Delta$,
    )),
    prooftree(rule(name: $RImpR(level, level)$, $Gamma seq(level) Delta, A -> B$, $A, Gamma seq(level) Delta, B$)),
  )

  #side-by-side(
    prooftree(rule(name: $RBoxGL(1, 1)$, $Box Gamma seq(1) Box A$, $Box Gamma, Gamma, Box A seq(1) A$)),
    prooftree(rule(name: $RBoxL(2, 2)$, $Box A, Gamma seq(2) Delta$, $A, Gamma seq(2) Delta$)),
  )


  The sequent calculus $GentzenD$ for $LogicD$, in which sequents of level $level = 1, 2, 3$ occur は，$GentzenS$ の規則にさらに $level = 3$ の規則および，次の $RLift(2, 3)$ を追加することで得られる．
  
  $
    #prooftree(rule(name: $RLift(2, 3)$, $Box Gamma seq(3) Box Delta$, $Box Gamma seq(2) Box Delta$))
  $
]

For the above calculi, the provability of $seq(1)$ is the same as that of the sequent calculus for $LogicGL$ (cf. @SV82).

@KKIM25 ではinitial sequentは任意の論理式 $A$ として $A seq(level) A$ によって導入されているが，ここでは $RAx(ell)$ を命題変数のみに制限している．
ただし，これは単に証明論的な埋め込みを考えるためのテクニカルな修正であり，実際には以下の補題より @KKIM25 と同等の証明能力を持っていると見做して良い．

#lemma[
  Let $A in FmlML$.
  1. $GentzenS proves A seq(ell) A$ where $level = 1, 2$.
  2. $GentzenD proves A seq(ell) A$ where $level = 1, 2, 3$.
] <lem:GentzenS_original_axioms>

#proof[
  We show by induction on $A$, uniformly in $ell = 1, 2$.
  If $A equiv p$, the claim follows from $RAx(ell)$.
  If $A equiv bot$, it follows from $RBotL(ell)$ and $RWR(ell, ell)$.
  The case $A equiv B -> C$ is proved by the following proof-tree:
  $
    #prooftree(rule(
      name: $RImpR(ell, ell)$,
      $B -> C seq(ell) B -> C$,
      rule(
        name: $RImpL(ell, ell)$,
        $B -> C, B seq(ell) C$,
        rule(name: $RWR(ell, ell)$, $B seq(ell) C, B$, ih($B seq(ell) B$)),
        rule(name: $RWL(ell, ell)$, $C, B seq(ell) C$, ih($C seq(ell) C$)),
      ),
    ))
  $

  The case $A equiv Box B$ is proved by the following proof-tree:
  $
    #prooftree(rule(
      name: $RBoxGL(1, 1)$,
      $Box B seq(1) Box B$,
      rule(name: $RWL(1, 1)$, $B, Box B seq(1) B$, ih($B seq(1) B$)),
    ))
  $
  When $level = 2$, we apply $RLift(1, 2)$ to obtain $Box B seq(2) Box B$.
  Moreover, when $level = 3$, we can apply $RLift(2, 3)$ to $Box B seq(2) Box B$ because antescent and succedent are $Box B$ form, so we can obtain $Box B seq(3) Box B$.
]

#proposition[Provability of $GentzenS$ @KKIM25[Proposition 3.5]][
  The following equivalences hold.
  + $GentzenS proves Gamma seq(1) Delta$ iff $LogicGL proves lconj Gamma -> ldisj Delta$.
  + $GentzenS proves Gamma seq(2) Delta$ iff $LogicS proves lconj Gamma -> ldisj Delta$.
] <prop:GentzenS_provability>

#proposition[Cut-admissibility of $GentzenS$][
  The cut rule is admissible in $GentzenS$.
  That is, when the cut rule $RCut(ell, ell)$ is defined as below, if $GentzenS + RCut(ell, ell) proves Gamma seq(ell) Delta$ then $GentzenS proves Gamma seq(ell) Delta$.
  $
    #prooftree(rule(
      name: $RCut(ell, ell)$,
      $Gamma_1, Gamma_2 seq(ell) Delta_1, Delta_2$,
      $Gamma_1 seq(ell) Delta_1, A$,
      $A, Gamma_2 seq(ell) Delta_2$,
    ))
  $
] <prop:GentzenS_cut_elimination>

同様の事実が $GentzenD$ でも成立する．

#proposition[Provability of $GentzenD$ @KKIM25[Proposition 3.6]][
  The following equivalences hold.
  + $GentzenD proves Gamma seq(1) Delta$ iff $LogicGL proves lconj Gamma -> ldisj Delta$.
  + $GentzenD proves Gamma seq(2) Delta$ iff $LogicS proves lconj Gamma -> ldisj Delta$.
  + $GentzenD proves Gamma seq(2) Delta$ iff $LogicD proves lconj Gamma -> ldisj Delta$.
] <prop:GentzenS_provability>

#proposition[Cut-admissibility of $GentzenD$ @KKIM25[Theorem 4.8]][
  The cut rule is admissible in $GentzenD$.
] <prop:GentzenS_cut_elimination>