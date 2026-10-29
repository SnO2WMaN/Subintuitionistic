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

Sequent calculi for provability logics have been well studied, particularly for $LogicGL$ @Lei81 @SV82 @Val83 @Bor83 @Avr84 @Moe01 @GR12 @Bri16 @GRS21.
Kushida @Kus20 proposed a new sequent calculus for $LogicS$, which has two levels of sequents $seq(1)$ and $seq(2)$,
and proved cut-elimination for the calculus.
Roughly speaking, sequents with $seq(1)$ correspond to provability in $LogicGL$ and sequents with $seq(2)$ correspond to provability in $LogicS$.
There is a lift-up rule from $seq(1)$ to $seq(2)$, but not vice versa.
Extending this approach, Kashima et al. @KKIM25 proposed a new sequent calculus for $LogicD$,
which has three levels of sequents $seq(1)$, $seq(2)$ and $seq(3)$.
Sequents with $seq(1)$ and $seq(2)$ correspond to provability in $LogicGL$ and $LogicS$, respectively, and sequents with $seq(3)$ correspond to provability in $LogicD$.

Another well-known result, due to Gödel, McKinsey and Tarski @God33 @MT48,
is that provability in propositional intuitionistic logic $LogicInt$ can be interpreted as provability in the modal logic $LogicSFour$
via a translation known as Gödel translation.
When such a correspondence holds, the modal logic is called a _modal companion_ of the propositional logic
(for instance, $LogicSFour$ is a modal companion of $LogicInt$).
It is well known which modal logics are the modal companions of logics stronger than $LogicInt$, that is, of superintuitionistic logics
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

== Acknowledgements

The author would like to thank Kohei Tominaga, Naoyuki Hatanaka, Haruka Kogure, and Taishi Kurahashi
for carefully reading the first draft of this paper
and providing valuable discussions and corrections of minor errors.

== Use of AI

The author declares that AI/LLMs were involved in the preparation of this paper.
While writing this draft, a review by Claude Fable pointed out a fatal error
in a part of the proof in @sect:Embedding_GentzenSPL_GentzenS as originally given.
This part was fixed with Claude, and the resulting arguments were verified by the author.
Any remaining errors are the sole responsibility of the author.

= Preliminaries <sect:preliminaries>

In this section, we introduce some notations and definitions that are used throughout the paper and mention some basic facts.
For more details, refer to the standard textbooks such as @Boo94 @CZ97.

Propositional variables are denoted by lowercase letters $p, q, r, dots$, and the set of all propositional variables is denoted by $PropVar$.
Formulas of propositional logic are constructed from propositional variables by the logical connectives $bot, and, or, ->$.
Formulas of modal logic are constructed from propositional variables by $bot, and, or, ->$ and the modal operator $Box$.
Other connectives are defined as usual.
Formulas of both propositional logic and modal logic are denoted by uppercase letters $A, B, C, dots$.
We write $FmlPL$ for the set of all formulas of propositional logic, and $FmlML$ for the set of all formulas of modal logic.
For our purpose, uppercase Greek letters $Gamma, Delta, dots$ denote _sets_ of formulas.
For a set $Gamma$ of modal formulas, we write $Box Gamma$ for the set ${Box A : A in Gamma}$.
Moreover, for a finite set $Gamma$, we write $lconj Gamma$ and $ldisj Gamma$ for the conjunction and the disjunction of all elements of $Gamma$,
respectively, where the empty conjunction $lconj emptyset$ and the empty disjunction $ldisj emptyset$ are understood as $top$ and $bot$.

Modal logic $LogicKFour$ is the smallest normal modal logic containing the axiom $Box A -> Box Box A$,
and Gödel-Löb provability logic $LogicGL$ is the smallest normal modal logic containing the axiom $Box (Box A -> A) -> Box A$.
Solovay's modal logic $LogicS$ is a non-normal extension of $LogicGL$ with the axiom $Box A -> A$;
that is, $LogicS$ is the smallest set of formulas that contains all theorems of $LogicGL$ and all instances of $Box A -> A$, and is closed under modus ponens only (but not under necessitation).
Japaridze's modal logic $LogicD$ is the non-normal extension of $LogicGL$ with the axioms $Box (Box A or Box B) -> Box A or Box B$ and $not Box bot$, defined analogously.
The following proposition can be shown by using the semantic tools for $LogicS$ and $LogicD$ developed in @Vis84 @Bek89.

#proposition[
  $LogicGL subset LogicD subset LogicS$.
  That is, $LogicGL proves A$ implies $LogicD proves A$, and $LogicD proves A$ implies $LogicS proves A$, but the converses do not hold.
]

The Gödel translation is a well-known embedding of intuitionistic propositional logic into modal logic.
However, for our purpose, we need a different translation, introduced by Visser @Vis81, which we call Visser's Gödel translation.

#definition[
  Visser's Gödel translation $(dot)^Vis : FmlPL -> FmlML$ is defined as follows.
  - $p^Vis = p and Box p$
  - $bot^Vis = bot$
  - $(A and B)^Vis = A^Vis and B^Vis$
  - $(A or B)^Vis = A^Vis or B^Vis$
  - $(A -> B)^Vis = Box (A^Vis -> B^Vis)$
] <defn:visser>

For a set $Gamma$ of propositional formulas, we write $Gamma^Vis$ for the set ${A^Vis : A in Gamma}$.

The difference between the original translation and Visser's lies only in the translation of propositional variables:
the original Gödel translation maps $p$ to $Box p$, while Visser's maps $p$ to $p and Box p$.

#proposition[@Vis81][
  Let $A in FmlPL$.
  - $LogicBPL proves A$ iff $LogicKFour proves A^Vis$.
  - $LogicFPL proves A$ iff $LogicGL proves A^Vis$.
]

Finally, we fix the proof-theoretic terminology used throughout this paper.
For the sequent calculi introduced in the following sections,
the notions of a proof-tree and its height, and of (height-preserving) admissible rules,
are defined as usual (see e.g. @TS00 @NvP11).
We write $sans(upright(G)) proves S$ if a sequent $S$ is derivable in a sequent calculus $sans(upright(G))$,
and $sans(upright(G)) provesh(h) S$ if $S$ is derivable in $sans(upright(G))$ by a proof-tree of height at most $h$.
For a formula $A$ and sets $Gamma, Delta$ of formulas, in the context of sequents,
we write $A, Gamma$ for ${A} union Gamma$ and $Gamma, Delta$ for $Gamma union Delta$.
Note that $A, Gamma = Gamma$ when $A in Gamma$, so that contraction is built into this notation.

= Sequent calculus $GentzenS$ for modal logic $LogicS$ <sect:GentzenS>

Although Kushida @Kus20 first introduced a sequent calculus for $LogicS$, his calculus is not suitable for our purpose.
Here we introduce a sequent calculus $GentzenS$ obtained by slightly modifying the sequent calculus for $LogicS$ due to Kashima and Kato @KK23.
We present below the definition of $GentzenS$ together with its basic proof-theoretic properties.

#definition[
  Let $Gamma, Delta$ be sets of formulas and let $ell = 1, 2$.
  An expression of the form $Gamma seq(ell) Delta$ is called a _sequent_.
  The sequent calculus $GentzenS$ for $LogicS$, in which sequents of level $ell = 1, 2$ occur, is defined by the following rules.

  #side-by-side(
    align: center + top,
    [
      #prooftree(rule(name: $RAx(ell)$, $p seq(ell) p$))
      where $p in PropVar$.
    ],
    prooftree(rule(name: $RBotL(ell)$, $bot seq(ell)$)),
  )

  #side-by-side(
    prooftree(rule(name: $RWL(ell, ell)$, $A, Gamma seq(ell) Delta$, $Gamma seq(ell) Delta$)),
    prooftree(rule(name: $RWR(ell, ell)$, $Gamma seq(ell) Delta, A$, $Gamma seq(ell) Delta$)),
  )

  $
    #prooftree(rule(name: $RLift(1, 2)$, $Gamma seq(2) Delta$, $Gamma seq(1) Delta$))
  $

  #side-by-side(
    prooftree(rule(name: $RAndL(ell, ell)$, $A and B, Gamma seq(ell) Delta$, $A, B, Gamma seq(ell) Delta$)),
    prooftree(rule(
      name: $RAndR(ell, ell)$,
      $Gamma seq(ell) Delta, A and B$,
      $Gamma seq(ell) Delta, A$,
      $Gamma seq(ell) Delta, B$,
    )),
  )

  #side-by-side(
    prooftree(rule(
      name: $ROrL(ell, ell)$,
      $A or B, Gamma seq(ell) Delta$,
      $A, Gamma seq(ell) Delta$,
      $B, Gamma seq(ell) Delta$,
    )),
    prooftree(rule(name: $ROrR(ell, ell)$, $Gamma seq(ell) Delta, A or B$, $Gamma seq(ell) Delta, A, B$)),
  )

  #side-by-side(
    prooftree(rule(
      name: $RImpL(ell, ell)$,
      $A -> B, Gamma seq(ell) Delta$,
      $Gamma seq(ell) Delta, A$,
      $B, Gamma seq(ell) Delta$,
    )),
    prooftree(rule(name: $RImpR(ell, ell)$, $Gamma seq(ell) Delta, A -> B$, $A, Gamma seq(ell) Delta, B$)),
  )

  #side-by-side(
    prooftree(rule(name: $RBoxGL(1, 1)$, $Box Gamma seq(1) Box A$, $Box Gamma, Gamma, Box A seq(1) A$)),
    prooftree(rule(name: $RBoxL(2, 2)$, $Box A, Gamma seq(2) Delta$, $A, Gamma seq(2) Delta$)),
  )
]

The provability of $seq(1)$ is the same as that of the sequent calculus for $LogicGL$ (cf. @SV82).

#remark[
  Our calculus differs from the system of @KK23 in two respects:
  the axiom $RAx(ell)$ is restricted to propositional variables, and the rules for $and$ and $or$ are adopted as primitive rules.
  Nevertheless, by suitably adapting the semantic arguments of @KK23, one can verify that the facts stated below,
  such as cut-admissibility and the coincidence of provability with that of $LogicS$, remain valid for our calculus.
] <rem:GentzenS_differences>

In particular, the identity sequents for arbitrary formulas, which are the axioms of the system of @KK23, are derivable.

#lemma[
  For every $A in FmlML$, $GentzenS proves A seq(ell) A$.
] <lem:GentzenS_original_axioms>

#proof[
  We show by induction on $A$, uniformly in $ell = 1, 2$.
  If $A equiv p$, the claim follows from $RAx(ell)$.
  If $A equiv bot$, it follows from $RBotL(ell)$ and $RWR(ell, ell)$.
  The cases $A equiv B and C$ and $A equiv B or C$ follow from the induction hypothesis by the rules for $and$ and $or$ together with weakening, as usual.
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
  When $ell = 2$, we apply $RLift(1, 2)$ to obtain $Box B seq(2) Box B$.
]

#proposition[Provability of $GentzenS$ @KK23][
  The following equivalences hold.
  + $GentzenS proves Gamma seq(1) Delta$ iff $LogicGL proves lconj Gamma -> ldisj Delta$.
  + $GentzenS proves Gamma seq(2) Delta$ iff $LogicS proves lconj Gamma -> ldisj Delta$.
] <prop:GentzenS_provability>

#proposition[Cut-admissibility of $GentzenS$ @KK23[Theorem 3.1]][
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

#lemma[Inversion rules $Inv(RImpL(ell, ell))$][
  In $GentzenS$ the inversion rules $Inv(RImpL(ell, ell))$ are height-preservingly admissible.
  #side-by-side(
    prooftree(rule(
      name: $Inv(RImpL(ell, ell))$,
      $GentzenS provesh(h) Gamma seq(ell) Delta, A$,
      $GentzenS provesh(h) A -> B, Gamma seq(ell) Delta$,
    )),
    prooftree(rule(
      name: $Inv(RImpL(ell, ell))$,
      $GentzenS provesh(h) B, Gamma seq(ell) Delta$,
      $GentzenS provesh(h) A -> B, Gamma seq(ell) Delta$,
    )),
  )
] <lem:GentzenS_inversion_ImpL>

#proof[
  We prove the two claims simultaneously by induction on the height of the proof-tree.
  In order to derive $A -> B, Gamma seq(ell) Delta$, the rules in which $A -> B$ can occur as the principal formula are the two rules $RWL(ell, ell)$ and $RImpL(ell, ell)$.
  For the other rules, and when $A -> B$ is not principal, the claim follows immediately from the induction hypothesis.
  The case of $RImpL(ell, ell)$ is also clear.
  In the case of $RWL(ell, ell)$ we have $GentzenS provesh(h-1) Gamma seq(ell) Delta$, so by means of $RWR(ell, ell)$ or $RWL(ell, ell)$ we obtain $GentzenS provesh(h) Gamma seq(ell) Delta, A$ and $GentzenS provesh(h) B, Gamma seq(ell) Delta$.
]

#lemma[Inversion rule $Inv(RImpR(ell, ell))$][
  In $GentzenS$ the inversion rule $Inv(RImpR(ell, ell))$ is height-preservingly admissible.
  $
    #prooftree(rule(
      name: $Inv(RImpR(ell, ell))$,
      $GentzenS provesh(h) A, Gamma seq(ell) Delta, B$,
      $GentzenS provesh(h) Gamma seq(ell) Delta, A -> B$,
    ))
  $
] <lem:GentzenS_inversion_ImpR>

#proof[
  We show by induction on the height of the proof-tree.
  In order to derive $Gamma seq(ell) Delta, A -> B$, the rules in which $A -> B$ can occur as the principal formula are the two rules $RWR(ell, ell)$ and $RImpR(ell, ell)$.
  For the other rules, and when $A -> B$ is not principal, the claim follows immediately from the induction hypothesis.
  These two rules are handled in the same way as in the case of $Inv(RImpL(ell, ell))$.
]

= Sequent calculus $GentzenSPL$ for propositional logic $LogicSPL$ <sect:GentzenSPL>

We define $GentzenSPL$, a modification of the sequent calculus for $LogicSPL$ due to Petrukhin @Pet23.

#definition[
  Take natural numbers $k >= 0$ and $n < 2^k$, and let $n = sum_(i=0)^(k-1) 2^i c_i$ be the $k$-bit binary representation of $n$.
  We then set $chevron.l n chevron.r^k_i = c_i$.
  To be explicit, $chevron.l 0 chevron.r^0_0 = 0$.
  Moreover, regarding $n$ as a $k$-bit string, we write $overline(n)$ for its one's complement.
  That is, for $k >= 1$ we have $chevron.l overline(n) chevron.r^k_i = 1 - chevron.l n chevron.r^k_i$, and $chevron.l overline(0) chevron.r^0_0 = 0$.
]

#definition[
  Let $Gamma, Delta$ be sets of formulas and let $ell = 1, 2$.
  An expression of the form $Gamma seq(ell) Delta$ is called a _sequent_.
  The sequent calculus $GentzenSPL$ for $LogicSPL$, in which sequents of level $ell = 1, 2$ occur, is defined by the following rules.

  #side-by-side(
    align: center + top,
    [
      #prooftree(rule(name: $RAx(ell)$, $p seq(ell) p$))
      where $p in PropVar$.
    ],
    prooftree(rule(name: $RBotL(ell)$, $bot seq(ell)$)),
  )

  #side-by-side(
    prooftree(rule(name: $RWL(ell, ell)$, $A, Gamma seq(ell) Delta$, $Gamma seq(ell) Delta$)),
    prooftree(rule(name: $RWR(ell, ell)$, $Gamma seq(ell) Delta, A$, $Gamma seq(ell) Delta$)),
  )

  $
    #prooftree(rule(name: $RLift(1, 2)$, $Gamma seq(2) Delta$, $Gamma seq(1) Delta$))
  $

  #side-by-side(
    prooftree(rule(name: $RAndL(ell, ell)$, $A and B, Gamma seq(ell) Delta$, $A, B, Gamma seq(ell) Delta$)),
    prooftree(rule(
      name: $RAndR(ell, ell)$,
      $Gamma seq(ell) Delta, A and B$,
      $Gamma seq(ell) Delta, A$,
      $Gamma seq(ell) Delta, B$,
    )),
  )

  #side-by-side(
    prooftree(rule(
      name: $ROrL(ell, ell)$,
      $A or B, Gamma seq(ell) Delta$,
      $A, Gamma seq(ell) Delta$,
      $B, Gamma seq(ell) Delta$,
    )),
    prooftree(rule(name: $ROrR(ell, ell)$, $Gamma seq(ell) Delta, A or B$, $Gamma seq(ell) Delta, A, B$)),
  )

  $
    #prooftree(rule(
      name: $RImpL(2, 2)$,
      $A -> B, Gamma seq(2) Delta$,
      $Gamma seq(2) Delta, A$,
      $B, Gamma seq(2) Delta$,
    ))
  $

  $
    #prooftree(rule(
      name: $RImpR(1, 1)$,
      $Sigma, {C_j -> D_j : 0 <= j < k} seq(1) A -> B$,
      $Delta_i, Sigma, A -> B, A seq(1) B, Gamma_i : 0 <= i < 2^k$,
    ))
  $

  where $k >= 0$ and the formulas $C_0, dots, C_(k-1)$ and $D_0, dots, D_(k-1)$ are arbitrary.
  Moreover, for $0 <= i < 2^k$ we set $Delta_i := {D_j : chevron.l i chevron.r^k_j = 1}$ and $Gamma_i := {C_j : chevron.l overline(i) chevron.r^k_j = 1}$.
  The expression displayed as the premise of $RImpR(1, 1)$ denotes the family of the $2^k$ sequents obtained by letting $i$ range over $0 <= i < 2^k$; that is, the rule $RImpR(1, 1)$ has $2^k$ premises.
]

Note that $RImpR(1, 1)$ corresponds to the rule in the sequent calculus for $LogicFPL$ given in @IKK01.

#example[
  The rule $RImpR(1, 1)$ for $k = 0, 1, 2$ takes the following forms.

  $k = 0$:
  $
    #prooftree(rule(name: $RImpR(1, 1)$, $Sigma seq(1) A -> B$, $Sigma, A -> B, A seq(1) B$))
  $

  $k = 1$:
  $
    #prooftree(rule(
      name: $RImpR(1, 1)$,
      $Sigma, C_0 -> D_0 seq(1) A -> B$,
      $D_0, Sigma, A -> B, A seq(1) B$,
      $Sigma, A -> B, A seq(1) B, C_0$,
    ))
  $

  $k = 2$:
  $
    #scale(85%, reflow: true, prooftree(rule(
      name: $RImpR(1, 1)$,
      $Sigma, C_0 -> D_0, C_1 -> D_1 seq(1) A -> B$,
      $D_0, D_1, Sigma, A -> B, A seq(1) B$,
      $D_0, Sigma, A -> B, A seq(1) B, C_1$,
      $D_1, Sigma, A -> B, A seq(1) B, C_0$,
      $Sigma, A -> B, A seq(1) B, C_0, C_1$,
    )))
  $
] <ex:GentzenSPL_ImpR>

As in @sect:GentzenS, although the rule $RAx(ell)$ is stated only for propositional variables, the identity sequent is derivable for every formula.

#lemma[
  For every $A in FmlPL$, $GentzenSPL proves A seq(ell) A$.
] <lem:GentzenSPL_axioms>

#proof[
  We show by induction on $A$, uniformly in $ell = 1, 2$.
  If $A equiv p$, the claim follows from $RAx(ell)$.
  If $A equiv bot$, it follows from $RBotL(ell)$ and $RWR(ell, ell)$.
  The cases $A equiv B and C$ and $A equiv B or C$ follow from the induction hypothesis by the rules for $and$ and $or$ together with weakening, as usual.
  For the case $A equiv B -> C$, we first derive $B -> C seq(1) B -> C$ by the following instance of $RImpR(1, 1)$ for $k = 1$ with $Sigma = emptyset$ and $C_0 -> D_0 := B -> C$.
  $
    #prooftree(rule(
      name: $RImpR(1, 1)$,
      $B -> C seq(1) B -> C$,
      rule(name: $RWL(1, 1)$, $C, B -> C, B seq(1) C$, ih($C seq(1) C$)),
      rule(name: [$RWL(1, 1)$, $RWR(1, 1)$], $B -> C, B seq(1) C, B$, ih($B seq(1) B$)),
    ))
  $
  When $ell = 2$, we further apply $RLift(1, 2)$.
]

We define _Solovay Propositional Logic_ $LogicSPL$ as the set of formulas ${A in FmlPL : GentzenSPL proves seq(2) A}$.

= Embedding of $GentzenSPL$ into $GentzenS$ <sect:Embedding_GentzenSPL_GentzenS>

We give a detailed proof of the embedding of $GentzenSPL$ into $GentzenS$ based on the proofs in @YS17 @Pet23.

#lemma[
  The following rule $RBoxKFour(1, ell)$ is admissible in $GentzenS$.
  $
    #prooftree(rule(name: $RBoxKFour(1, ell)$, $Box Gamma seq(ell) Box A$, $Box Gamma, Gamma seq(1) A$))
  $
] <lem:GentzenS_admits_BoxK4>

#proof[
  For $ell = 1$, the claim is proved by the following proof-tree:
  $
    #prooftree(rule(
      name: $RBoxGL(1, 1)$,
      $Box Gamma seq(1) Box A$,
      rule(name: $RWL(1, 1)$, $Gamma, Box Gamma, Box A seq(1) A$, $Gamma, Box Gamma seq(1) A$),
    ))
  $
  When $ell = 2$, we further apply $RLift(1, 2)$ to obtain $Box Gamma seq(2) Box A$.
]

#lemma[cf. @YS17[Lemma 3]][
  For every $A in FmlPL$, $GentzenS proves A^Vis seq(ell) Box A^Vis$.
] <lem:embedding_SPL_to_S_aux1>

#proof[
  We show by induction on $A$. The cases $A equiv bot$ and $A equiv B or C$ are omitted.

  *Case* $A equiv p$:
  $
    #prooftree(rule(
      name: $RAndL(ell, ell)$,
      $p and Box p seq(ell) Box (p and Box p)$,
      rule(
        name: $RWL(ell, ell)$,
        $p, Box p seq(ell) Box (p and Box p)$,
        rule(
          name: $RBoxKFour(1, ell)$,
          $Box p seq(ell) Box (p and Box p)$,
          rule(
            name: $RAndR(1, 1)$,
            $Box p, p seq(1) p and Box p$,
            noted([(@lem:GentzenS_original_axioms, $RWL(1, 1)$)], $Box p, p seq(1) p$),
            noted([(@lem:GentzenS_original_axioms, $RWL(1, 1)$)], $Box p, p seq(1) Box p$),
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
          rule(name: $RWL(ell, ell)$, $B^Vis, C^Vis seq(ell) Box B^Vis$, ih($B^Vis seq(ell) Box B^Vis$)),
          rule(name: $RWL(ell, ell)$, $B^Vis, C^Vis seq(ell) Box C^Vis$, ih($C^Vis seq(ell) Box C^Vis$)),
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
                [(@lem:GentzenS_original_axioms, $RWL(1, 1)$)],
                $B^Vis, C^Vis, Box B^Vis, Box C^Vis seq(1) B^Vis$,
              ),
              noted(
                [(@lem:GentzenS_original_axioms, $RWL(1, 1)$)],
                $B^Vis, C^Vis, Box B^Vis, Box C^Vis seq(1) C^Vis$,
              ),
            ),
          ),
        ),
      ),
    ))
  $
  Here the use of the cut rule $RCut(ell, ell)$ is legitimate by @prop:GentzenS_cut_elimination; we use the cut rule freely in proof-trees in what follows.

  *Case* $A equiv B -> C$:
  $
    #prooftree(rule(
      name: $RBoxKFour(1, ell)$,
      $Box (B^Vis -> C^Vis) seq(ell) Box Box (B^Vis -> C^Vis)$,
      noted(
        [(@lem:GentzenS_original_axioms, $RWL(1, 1)$)],
        $Box (B^Vis -> C^Vis), B^Vis -> C^Vis seq(1) Box (B^Vis -> C^Vis)$,
      ),
    ))
  $
]

#lemma[cf. @YS17[Lemma 5]][
  The following rule is admissible in $GentzenS$.
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
        name: $RWL(1, 1)$,
        $Box Sigma^Vis, Sigma^Vis, Box Gamma, Gamma, Box A seq(1) A$,
        $Sigma^Vis, Gamma, Box A seq(1) A$,
      ),
    ))
  $
  Now, by @lem:embedding_SPL_to_S_aux1, for every $B in Sigma$ we have $GentzenS proves B^Vis seq(1) Box B^Vis$.
  Hence, by applying $RCut(1, 1)$ an appropriate number of times to successively replace the elements of $Box Sigma^Vis$, we obtain $Sigma^Vis, Box Gamma seq(1) Box A$.
  When $ell = 2$, we further apply $RLift(1, 2)$.
]

#lemma[@Pet23[Lemma 4]][
  If $GentzenSPL proves Gamma seq(ell) Delta$, then $GentzenS proves Gamma^Vis seq(ell) Delta^Vis$.
] <lem:embedding_SPL_to_S>

#proof[
  We show by induction on the height of the proof-tree.
  We treat in particular the cases of $RImpL(2, 2)$ and $RImpR(1, 1)$.

  *Case* $RImpL(2, 2)$:
  Suppose the rule we now wish to consider has the following form.
  $
    #prooftree(rule(
      name: $RImpL(2, 2)$,
      $GentzenSPL provesh(h) A -> B, Gamma seq(2) Delta$,
      $GentzenSPL provesh(h-1) Gamma seq(2) Delta, A$,
      $GentzenSPL provesh(h-1) B, Gamma seq(2) Delta$,
    ))
  $
  Then, by the induction hypothesis, we have $GentzenS proves Gamma^Vis seq(2) Delta^Vis, A^Vis$ and $GentzenS proves B^Vis, Gamma^Vis seq(2) Delta^Vis$.
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
  This is nothing but $GentzenS proves (A -> B)^Vis, Gamma^Vis seq(2) Delta^Vis$.

  *Case* $RImpR(1, 1)$:
  Fix $k$, and suppose the rule we now wish to consider has the following form.
  $
    #prooftree(rule(
      name: $RImpR(1, 1)$,
      $GentzenSPL provesh(h) Sigma, {C_j -> D_j : 0 <= j < k} seq(1) A -> B$,
      $GentzenSPL provesh(h-1) Delta_i, Sigma, A -> B, A seq(1) B, Gamma_i : 0 <= i < 2^k$,
    ))
  $
  By the induction hypothesis, for every $i$ with $0 <= i < 2^k$ we have $GentzenS proves Delta_i^Vis, Sigma^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis, Gamma_i^Vis$.
  By combining these sequents with $2^k - 1$ appropriate applications of $RImpL(1, 1)$, we obtain
  $GentzenS proves Sigma^Vis, {C_j^Vis -> D_j^Vis : 0 <= j < k}, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$.
  We illustrate the case $k = 2$ below; the construction is easy to generalize to arbitrary $k$.
  Let $cal(D)_1$ and $cal(D)_2$ be the following proof-trees.
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

  The rest can be carried out as follows.
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
  This is nothing but $GentzenS proves Sigma^Vis, {C_j -> D_j : 0 <= j < k}^Vis seq(1) (A -> B)^Vis$.
]

Following the strategy of @YS17[Lemma 7], we prove the converse direction in the following strengthened form.

#lemma[
  Let $Gamma, Delta$ be sets of propositional formulas and let $Phi_1, Phi_2, Psi$ be sets of propositional variables.
  If $GentzenS proves Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, Delta^Vis$,
  then $GentzenSPL proves Gamma, Phi_1, Phi_2 seq(ell) Psi, Delta$.
] <lem:embedding_S_to_SPL_general>

#proof[
  First, observe that every formula occurring in the assumed sequent is of exactly one of the following forms:
  a translation $A^Vis$, which is either $bot$ or has $and$, $or$ or $Box$ as its outermost connective;
  a propositional variable; or a boxed propositional variable.
  In particular, no formula in the sequent is an implication,
  and hence the last rule of a proof-tree of the assumed sequent is neither $RImpL(ell, ell)$ nor $RImpR(ell, ell)$.
  With this in mind, we prove the claim by induction on the height of the proof-tree,
  distinguishing cases according to the last rule and the position of its principal formula.

  Note that the statement is generalized over $Gamma, Delta, Phi_1, Phi_2$ and $Psi$:
  in each case below, the premise of the last rule is re-decomposed into the form $Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, Delta^Vis$, possibly with components different from those of the conclusion, and the induction hypothesis is applied to this decomposition.
  We illustrate this point concretely in the case $RAndL(ell, ell)$ below.

  *Case* $RAx(ell)$:
  The sequent is $p seq(ell) p$, that is, $Gamma = Delta = Phi_2 = emptyset$ and $Phi_1 = Psi = {p}$.
  The rule $RAx(ell)$ of $GentzenSPL$ yields the desired $GentzenSPL proves p seq(ell) p$.

  *Case* $RBotL(ell)$:
  The sequent is $bot seq(ell)$, that is, $Gamma = {bot}$ and all the other components are empty.
  The rule $RBotL(ell)$ of $GentzenSPL$ yields the desired sequent.

  *Case* $RWL(ell, ell)$, $RWR(ell, ell)$, $RLift(1, 2)$:
  These follow straightforwardly from the induction hypothesis and the corresponding rule of $GentzenSPL$.
  We only note that no weakening is needed in $GentzenSPL$ when $RWL(ell, ell)$ introduces a variable $p in Phi_1$ with $p in Phi_2$, or a boxed variable $Box p$ with $p in Phi_1$:
  in these cases the antecedent of the sequent given by the induction hypothesis already coincides with $Gamma, Phi_1, Phi_2$ as a set.

  *Case* $RAndL(ell, ell)$:
  The principal formula is either $p^Vis = p and Box p$ for some $p in Gamma$, or $(A and B)^Vis = A^Vis and B^Vis$ for some $A and B in Gamma$.
  In the former case, the application we are concerned with is the following.
  $
    #prooftree(rule(
      name: $RAndL(ell, ell)$,
      $GentzenS provesh(h) p and Box p, (Gamma without {p})^Vis, Phi_1, Box Phi_2 seq(ell) Psi, Delta^Vis$,
      $GentzenS provesh(h-1) p, Box p, (Gamma without {p})^Vis, Phi_1, Box Phi_2 seq(ell) Psi, Delta^Vis$,
    ))
  $
  Here we re-decompose the premise:
  it is of the form $Gamma'^Vis, Phi'_1, Box Phi'_2 seq(ell) Psi, Delta^Vis$ with $Gamma' := Gamma without {p}$, $Phi'_1 := Phi_1 union {p}$ and $Phi'_2 := Phi_2 union {p}$,
  which differ from the components $Gamma, Phi_1, Phi_2$ of the conclusion.
  Applying the induction hypothesis to this decomposition yields $GentzenSPL proves Gamma without {p}, Phi_1, Phi_2, p seq(ell) Psi, Delta$,
  whose antecedent coincides with $Gamma, Phi_1, Phi_2$ as a set, since $p in Gamma$.

  In the latter case, the application we are concerned with is the following.
  $
    #prooftree(rule(
      name: $RAndL(ell, ell)$,
      $GentzenS provesh(h) A^Vis and B^Vis, (Gamma without {A and B})^Vis, Phi_1, Box Phi_2 seq(ell) Psi, Delta^Vis$,
      $GentzenS provesh(h-1) A^Vis, B^Vis, (Gamma without {A and B})^Vis, Phi_1, Box Phi_2 seq(ell) Psi, Delta^Vis$,
    ))
  $
  The induction hypothesis applied to the premise yields $GentzenSPL proves A, B, Gamma without {A and B}, Phi_1, Phi_2 seq(ell) Psi, Delta$,
  and $RAndL(ell, ell)$ of $GentzenSPL$ yields the desired sequent.

  *Case* $RAndR(ell, ell)$:
  The principal formula is either $p^Vis$ for some $p in Delta$, or $(A and B)^Vis$ for some $A and B in Delta$.
  In the former case, the application we are concerned with is the following.
  $
  #prooftree(rule(
    name: $RAndR(ell, ell)$,
    $GentzenS provesh(h) Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, p and Box p, (Delta without {p})^Vis$,
    $GentzenS provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, p, (Delta without {p})^Vis$,
    $GentzenS provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, Box p, (Delta without {p})^Vis$,
  ))
  $
  The induction hypothesis applied to the left premise yields
  $GentzenSPL proves Gamma, Phi_1, Phi_2 seq(ell) Psi, p, Delta without {p}$,
  whose succedent coincides with $Psi, Delta$ as a set, since $p in Delta$.
  Note that the right premise, whose succedent contains the boxed variable $Box p$, is simply not used.

  In the latter case, the application we are concerned with is the following.
  $
    #prooftree(rule(
      name: $RAndR(ell, ell)$,
      $GentzenS provesh(h) Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, A^Vis and B^Vis, (Delta without {A and B})^Vis$,
      $GentzenS provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, A^Vis, (Delta without {A and B})^Vis$,
      $GentzenS provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, B^Vis, (Delta without {A and B})^Vis$,
    ))
  $
  The induction hypothesis applies to both premises, and $RAndR(ell, ell)$ of $GentzenSPL$ yields the desired sequent.

  *Case* $ROrL(ell, ell)$, $ROrR(ell, ell)$:
  The principal formula can only be $(A or B)^Vis = A^Vis or B^Vis$ for some $A or B in Gamma$ (resp. $A or B in Delta$).
  The induction hypothesis applies to the premises, and the corresponding rule of $GentzenSPL$ yields the desired sequent.

  *Case* $RBoxL(2, 2)$:
  The principal formula is either $Box p$ for some $p in Phi_2$, or $(E -> F)^Vis = Box(E^Vis -> F^Vis)$ for some $E -> F in Gamma$.

  In the former case, the application we are concerned with is the following.
  $
    #prooftree(rule(
      name: $RBoxL(2, 2)$,
      $GentzenS provesh(h) Box p, Gamma^Vis, Phi_1, Box(Phi_2 without {p}) seq(2) Psi, Delta^Vis$,
      $GentzenS provesh(h-1) p, Gamma^Vis, Phi_1, Box(Phi_2 without {p}) seq(2) Psi, Delta^Vis$,
    ))
  $
  The induction hypothesis applied to the premise, with the components $Phi_1 union {p}$ and $Phi_2 without {p}$, yields
  $GentzenSPL proves Gamma, Phi_1, p, Phi_2 without {p} seq(2) Psi, Delta$,
  whose antecedent coincides with $Gamma, Phi_1, Phi_2$ as a set, since $p in Phi_2$.

  In the latter case, the application we are concerned with is the following.
  $
    #prooftree(rule(
      name: $RBoxL(2, 2)$,
      $GentzenS provesh(h) Box(E^Vis -> F^Vis), (Gamma without {E -> F})^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
      $GentzenS provesh(h-1) E^Vis -> F^Vis, (Gamma without {E -> F})^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
    ))
  $
  Applying the height-preserving inversion $Inv(RImpL(2, 2))$ (@lem:GentzenS_inversion_ImpL) to the premise, we obtain the following.
  $
    GentzenS & provesh(h-1) (Gamma without {E -> F})^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis, E^Vis \
    GentzenS & provesh(h-1) F^Vis, (Gamma without {E -> F})^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis.
  $
  Since the height is $h - 1$, the induction hypothesis applies and yields the following.
  $
    GentzenSPL & proves (Gamma without {E -> F}), Phi_1, Phi_2 seq(2) Psi, Delta, E \
    GentzenSPL & proves F, (Gamma without {E -> F}), Phi_1, Phi_2 seq(2) Psi, Delta.
  $
  Using $RImpL(2, 2)$ we obtain $GentzenSPL proves E -> F, (Gamma without {E -> F}), Phi_1, Phi_2 seq(2) Psi, Delta$, that is, $GentzenSPL proves Gamma, Phi_1, Phi_2 seq(2) Psi, Delta$.

  *Case* $RBoxGL(1, 1)$:
  Since the antecedent of the conclusion of an application of $RBoxGL(1, 1)$ consists of boxed formulas only and its succedent consists of exactly one boxed formula,
  we have $Phi_1 = Psi = emptyset$, $Gamma = {C_j -> D_j : 0 <= j < k}$ for some $k >= 0$ and formulas $C_j, D_j$ ($0 <= j < k$), and $Delta = {E -> F}$ for some formulas $E, F$.
  The application we are concerned with is thus the following.
  $
    #prooftree(rule(
      name: $RBoxGL(1, 1)$,
      $GentzenS provesh(h) Box{C^Vis_j -> D^Vis_j : 0 <= j < k}, Box Phi_2 seq(1) Box(E^Vis -> F^Vis)$,
      $GentzenS provesh(h-1) {C^Vis_j -> D^Vis_j : 0 <= j < k}, Phi_2, Box{C^Vis_j -> D^Vis_j : 0 <= j < k}, Box Phi_2, Box(E^Vis -> F^Vis) seq(1) E^Vis -> F^Vis$,
    ))
  $
  Applying the height-preserving inversion $Inv(RImpR(1, 1))$ (@lem:GentzenS_inversion_ImpR) to the premise, we obtain the following.
  $
    GentzenS provesh(h-1) {C^Vis_j -> D^Vis_j : 0 <= j < k}, Phi_2, Box{C^Vis_j -> D^Vis_j : 0 <= j < k}, Box Phi_2, Box(E^Vis -> F^Vis), E^Vis seq(1) F^Vis.
  $
  Furthermore, the height-preserving inversion $Inv(RImpL(1, 1))$ (@lem:GentzenS_inversion_ImpL) applies to the members of ${C^Vis_j -> D^Vis_j : 0 <= j < k}$, so, following the definition of $RImpR(1, 1)$ in $GentzenSPL$ and determining $Gamma_i, Delta_i$ from $C_0, dots, C_(k-1)$ and $D_0, dots, D_(k-1)$, for each $i$ with $0 <= i < 2^k$ we obtain the following.
  $
    GentzenS provesh(h-1) Delta^Vis_i, Phi_2, Box{C^Vis_j -> D^Vis_j : 0 <= j < k}, Box Phi_2, Box(E^Vis -> F^Vis), E^Vis seq(1) F^Vis, Gamma^Vis_i.
  $
  Each of these sequents is again of the form required in the statement:
  since $Box{C^Vis_j -> D^Vis_j : 0 <= j < k} = {C_j -> D_j : 0 <= j < k}^Vis$ and $Box(E^Vis -> F^Vis) = (E -> F)^Vis$,
  its antecedent consists of the translations of $Delta_i, {C_j -> D_j : 0 <= j < k}, E -> F, E$, the variables $Phi_2$, and the boxed variables $Box Phi_2$.
  Since the height is $h - 1$, the induction hypothesis applies and yields the following.
  $
    GentzenSPL proves Delta_i, {C_j -> D_j : 0 <= j < k}, E -> F, E, Phi_2 seq(1) F, Gamma_i.
  $
  Applying $RImpR(1, 1)$ of $GentzenSPL$ with $Sigma := {C_j -> D_j : 0 <= j < k} union Phi_2$ to these premises, we obtain the following, where we note that antecedents are sets and hence the duplicated occurrences of $C_j -> D_j$ are contracted.
  $
    GentzenSPL proves {C_j -> D_j : 0 <= j < k}, Phi_2 seq(1) E -> F.
  $
  This is the desired sequent $Gamma, Phi_1, Phi_2 seq(1) Psi, Delta$.
]

#lemma[@Pet23[Lemma 5]][
  If $GentzenS proves Gamma^Vis seq(ell) Delta^Vis$, then $GentzenSPL proves Gamma seq(ell) Delta$.
] <lem:embedding_S_to_SPL>

#proof[
  Take $Phi_1 = Phi_2 = Psi = emptyset$ in @lem:embedding_S_to_SPL_general.
]

#theorem[@Pet23[Theorem 1]][
  $GentzenSPL proves Gamma seq(ell) Delta$ iff $GentzenS proves Gamma^Vis seq(ell) Delta^Vis$.
] <thm:embedding_GentzenSPL_GentzenS>

#proof[
  This follows by combining @lem:embedding_SPL_to_S and @lem:embedding_S_to_SPL.
]

Combining @thm:embedding_GentzenSPL_GentzenS with the properties of $GentzenS$ (Propositions #thmnumber(<prop:GentzenS_provability>) and #thmnumber(<prop:GentzenS_cut_elimination>)), we immediately obtain the following corollaries.

#corollary[
  $LogicSPL proves A$ iff $LogicS proves A^Vis$ for every $A in FmlPL$.
] <cor:embedding_GentzenSPL_S>

#corollary[Cut-admissibility of $GentzenSPL$][
  In $GentzenSPL$, the cut rule $RCut(ell, ell)$ is admissible.
] <cor:GentzenSPL_cut_elimination>

#remark[
  It should be noted that this embedding proof, and consequently @cor:GentzenSPL_cut_elimination,
  cannot be regarded as purely syntactic in the strict sense.
  In Lemmas #thmnumber(<lem:embedding_SPL_to_S_aux1>) and #thmnumber(<lem:embedding_SPL_to_S_aux2>) we use the cut,
  relying on the fact that cut is admissible in $GentzenS$.
  The sequent calculus for $LogicS$ proposed by @Kus20 comes with a purely syntactic cut-elimination algorithm;
  however, the cut-admissibility of $GentzenS$ from @KK23 that we adopt here
  (more precisely, the system modified by adding $and$ and $or$ as primitive rules)
  is established by a semantic argument.
  Consequently, for instance, we cannot construct a cut-free proof-tree of $GentzenSPL$ explicitly from this proof.
] <rem:syntacticality_embedding>

#remark[About $LogicFPL$ and $LogicGL$][
  As also suggested by Petrukhin's paper,
  if one is given a suitable sequent calculus for $LogicFPL$ (that is, roughly speaking, the fragment of $GentzenSPL$ restricted to sequents $seq(1)$)
  and a sequent calculus for $LogicGL$ (likewise, the fragment of $GentzenS$ restricted to sequents $seq(1)$, which coincides with @SV82),
  then, by reconstructing the argument above while forgetting about $seq(2)$,
  one obtains a syntactic construction of the embedding of $LogicFPL$ into $LogicGL$ established in @Vis81.
]

== Errors in Petrukhin's proof <sect:errors_in_Petrukhin>

This embedding result is based on Petrukhin @Pet23, but the proof in the original paper appears to contain several errors.
We point them out below.
The issue concerns @Pet23[Lemma 5], which corresponds to @lem:embedding_S_to_SPL in the present paper.

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

= Sequent calculus $GentzenD$ for modal logic $LogicD$ <sect:GentzenD>

Kashima et al. @KKIM25 introduced two sequent calculi for $LogicD$: one using only two-level sequents and another using three-level sequents#footnote[Cut-elimination does not hold for their two-level calculus, so it is not suitable for our purpose (cf. @KKIM25[Theorem 4.9]).].
Here we present the system $GentzenD$, obtained by modifying their three-level calculus in the same way as in @sect:GentzenS, together with its basic proof-theoretic properties.

#definition[
  Let $Gamma, Delta$ be sets of formulas and let $ell = 1, 2, 3$.
  An expression of the form $Gamma seq(ell) Delta$ is called a _sequent_.
  The sequent calculus $GentzenD$ for $LogicD$, in which sequents of level $ell = 1, 2, 3$ occur, is defined by the following rules.

  #side-by-side(
    align: center + top,
    [
      #prooftree(rule(name: $RAx(ell)$, $p seq(ell) p$))
      where $p in PropVar$.
    ],
    prooftree(rule(name: $RBotL(ell)$, $bot seq(ell)$)),
  )

  #side-by-side(
    prooftree(rule(name: $RWL(ell, ell)$, $A, Gamma seq(ell) Delta$, $Gamma seq(ell) Delta$)),
    prooftree(rule(name: $RWR(ell, ell)$, $Gamma seq(ell) Delta, A$, $Gamma seq(ell) Delta$)),
  )

  #side-by-side(
    prooftree(rule(name: $RAndL(ell, ell)$, $A and B, Gamma seq(ell) Delta$, $A, B, Gamma seq(ell) Delta$)),
    prooftree(rule(
      name: $RAndR(ell, ell)$,
      $Gamma seq(ell) Delta, A and B$,
      $Gamma seq(ell) Delta, A$,
      $Gamma seq(ell) Delta, B$,
    )),
  )

  #side-by-side(
    prooftree(rule(
      name: $ROrL(ell, ell)$,
      $A or B, Gamma seq(ell) Delta$,
      $A, Gamma seq(ell) Delta$,
      $B, Gamma seq(ell) Delta$,
    )),
    prooftree(rule(name: $ROrR(ell, ell)$, $Gamma seq(ell) Delta, A or B$, $Gamma seq(ell) Delta, A, B$)),
  )

  #side-by-side(
    prooftree(rule(
      name: $RImpL(ell, ell)$,
      $A -> B, Gamma seq(ell) Delta$,
      $Gamma seq(ell) Delta, A$,
      $B, Gamma seq(ell) Delta$,
    )),
    prooftree(rule(name: $RImpR(ell, ell)$, $Gamma seq(ell) Delta, A -> B$, $A, Gamma seq(ell) Delta, B$)),
  )

  #side-by-side(
    prooftree(rule(name: $RLift(1, 2)$, $Gamma seq(2) Delta$, $Gamma seq(1) Delta$)),
    prooftree(rule(name: $RLift(2, 3)$, $Box Gamma seq(3) Box Delta$, $Box Gamma seq(2) Box Delta$)),
  )

  #side-by-side(
    prooftree(rule(name: $RBoxGL(1, 1)$, $Box Gamma seq(1) Box A$, $Box Gamma, Gamma, Box A seq(1) A$)),
    prooftree(rule(name: $RBoxL(2, 2)$, $Box A, Gamma seq(2) Delta$, $A, Gamma seq(2) Delta$)),
  )
]

The provability of $seq(1)$ and $seq(2)$ coincides with that of $GentzenS$, and the level-$3$ sequents $seq(3)$ capture provability in $LogicD$.

#remark[
  Our calculus differs from the three-level system of @KKIM25 in the same two respects as in @rem:GentzenS_differences,
  and the facts stated below are likewise recovered semantically.
]

In particular, the identity sequents for arbitrary formulas are derivable.

#lemma[
  For every $A in FmlML$, $GentzenD proves A seq(ell) A$.
] <lem:GentzenD_axioms>

#proof[
  The argument is the same as for @lem:GentzenS_original_axioms.
]

#proposition[Provability of $GentzenD$ @KKIM25[Proposition 3.6]][
  The following equivalences hold.
  + $GentzenD proves Gamma seq(1) Delta$ iff $LogicGL proves lconj Gamma -> ldisj Delta$.
  + $GentzenD proves Gamma seq(2) Delta$ iff $LogicS proves lconj Gamma -> ldisj Delta$.
  + $GentzenD proves Gamma seq(3) Delta$ iff $LogicD proves lconj Gamma -> ldisj Delta$.
] <prop:GentzenD_provability>

#proposition[Cut-admissibility of $GentzenD$ @KKIM25[Theorem 4.8]][
  The cut rule is admissible in $GentzenD$.
  That is, with the cut rule $RCut(ell, ell)$ defined as below, if $GentzenD + RCut(ell, ell) proves Gamma seq(ell) Delta$ then $GentzenD proves Gamma seq(ell) Delta$.
  $
    #prooftree(rule(
      name: $RCut(ell, ell)$,
      $Gamma_1, Gamma_2 seq(ell) Delta_1, Delta_2$,
      $Gamma_1 seq(ell) Delta_1, A$,
      $A, Gamma_2 seq(ell) Delta_2$,
    ))
  $
] <prop:GentzenD_cut_elimination>

#lemma[Inversion rules $Inv(RImpL(ell, ell))$, $Inv(RImpR(ell, ell))$][
  In $GentzenD$ the inversion rules $Inv(RImpL(ell, ell))$ and $Inv(RImpR(ell, ell))$ are height-preservingly admissible.

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

  $
    #prooftree(rule(
      name: $Inv(RImpR(ell, ell))$,
      $GentzenD provesh(h) A, Gamma seq(ell) Delta, B$,
      $GentzenD provesh(h) Gamma seq(ell) Delta, A -> B$,
    ))
  $
] <lem:GentzenD_inversion>

#proof[
  The argument is the same as for Lemmas #thmnumber(<lem:GentzenS_inversion_ImpL>) and #thmnumber(<lem:GentzenS_inversion_ImpR>).
]

= Sequent calculus $GentzenDPL$ for propositional logic $LogicDPL$ <sect:GentzenDPL>

We define $GentzenDPL$, the sequent calculus for $LogicDPL$, which is obtained by adding to $GentzenSPL$ a single rule $RLift(2, 3)$ that arises naturally from the lift rule of $GentzenD$.

#definition[
  Let $Gamma, Delta$ be sets of formulas and let $ell = 1, 2, 3$.
  An expression of the form $Gamma seq(ell) Delta$ is called a _sequent_.
  The sequent calculus $GentzenDPL$ for $LogicDPL$, in which sequents of level $ell = 1, 2, 3$ occur, is defined by the following rules.

  #side-by-side(
    align: center + top,
    [
      #prooftree(rule(name: $RAx(ell)$, $p seq(ell) p$))
      where $p in PropVar$.
    ],
    prooftree(rule(name: $RBotL(ell)$, $bot seq(ell)$)),
  )

  #side-by-side(
    prooftree(rule(name: $RWL(ell, ell)$, $A, Gamma seq(ell) Delta$, $Gamma seq(ell) Delta$)),
    prooftree(rule(name: $RWR(ell, ell)$, $Gamma seq(ell) Delta, A$, $Gamma seq(ell) Delta$)),
  )

  #side-by-side(
    prooftree(rule(name: $RAndL(ell, ell)$, $A and B, Gamma seq(ell) Delta$, $A, B, Gamma seq(ell) Delta$)),
    prooftree(rule(
      name: $RAndR(ell, ell)$,
      $Gamma seq(ell) Delta, A and B$,
      $Gamma seq(ell) Delta, A$,
      $Gamma seq(ell) Delta, B$,
    )),
  )

  #side-by-side(
    prooftree(rule(
      name: $ROrL(ell, ell)$,
      $A or B, Gamma seq(ell) Delta$,
      $A, Gamma seq(ell) Delta$,
      $B, Gamma seq(ell) Delta$,
    )),
    prooftree(rule(name: $ROrR(ell, ell)$, $Gamma seq(ell) Delta, A or B$, $Gamma seq(ell) Delta, A, B$)),
  )

  #side-by-side(
    prooftree(rule(
      name: $RImpL(2, 2)$,
      $A -> B, Gamma seq(2) Delta$,
      $Gamma seq(2) Delta, A$,
      $B, Gamma seq(2) Delta$,
    )),
    prooftree(rule(name: $RLift(1, 2)$, $Gamma seq(2) Delta$, $Gamma seq(1) Delta$)),
  )

  $
    #prooftree(rule(
      name: $RImpR(1, 1)$,
      $Sigma, {C_j -> D_j : 0 <= j < k} seq(1) A -> B$,
      $Delta_i, Sigma, A -> B, A seq(1) B, Gamma_i : 0 <= i < 2^k$,
    ))
  $

  #align(center)[where $k$, $Delta_i$ and $Gamma_i$ are defined in the same way as in $GentzenSPL$.]

  $
    #prooftree(rule(
      name: $RLift(2, 3)$,
      ${A_i -> B_i : 0 <= i < n}, Phi seq(3) {C_j -> D_j : 0 <= j < m}$,
      ${A_i -> B_i : 0 <= i < n}, Phi seq(2) {C_j -> D_j : 0 <= j < m}$,
    ))
  $

  #align(center)[
    where $n, m >= 0$, the formulas $A_0, dots, A_(n-1), B_0, dots, B_(n-1), C_0, dots, C_(m-1), D_0, dots, D_(m-1)$ are arbitrary, and $Phi$ is a set of propositional variables.
  ]
]

The reason why propositional variables are allowed to occur in the antecedent of $RLift(2, 3)$, but not in the succedent, will be explained in @sect:Embedding_GentzenDPL_GentzenD (Lemmas #thmnumber(<lem:GD_box_to_Vis>) and #thmnumber(<lem:GD_Vis_to_box>), and @rem:Lift_no_succedent_variables).

As in @sect:GentzenSPL, the identity sequent is derivable for every formula.

#lemma[
  For every $A in FmlPL$, $GentzenDPL proves A seq(ell) A$.
] <lem:GentzenDPL_axioms>

#proof[
  The argument is the same as for @lem:GentzenSPL_axioms.
  When $ell = 3$ and $A equiv B -> C$, we further apply $RLift(2, 3)$ to $B -> C seq(2) B -> C$, which is applicable since both sides consist of implications.
]

We define _Dzhaparidze Propositional Logic_ $LogicDPL$ as the set of formulas ${A in FmlPL : GentzenDPL proves seq(3) A}$.

= Embedding of $GentzenDPL$ into $GentzenD$ <sect:Embedding_GentzenDPL_GentzenD>

The embedding of $GentzenDPL$ into $GentzenD$ is obtained by adapting the argument of @sect:Embedding_GentzenSPL_GentzenS,
where the only new rule is $RLift(2, 3)$.

#lemma[
  The rule $RBoxKFour(1, ell)$ is admissible in $GentzenD$.
  $
    #prooftree(rule(name: $RBoxKFour(1, ell)$, $Box Gamma seq(ell) Box A$, $Box Gamma, Gamma seq(1) A$))
  $
] <lem:GentzenD_admits_BoxK4>

#proof[
  As in @lem:GentzenS_admits_BoxK4, we first obtain $Box Gamma seq(1) Box A$.
  When $ell = 2$, we apply $RLift(1, 2)$, and when $ell = 3$, we apply $RLift(1, 2)$ and $RLift(2, 3)$, the latter being applicable since both $Box Gamma$ and $Box A$ consist of boxed formulas.
]

#lemma[
  For every $A in FmlPL$, $GentzenD proves A^Vis seq(ell) Box A^Vis$.
] <lem:embedding_DPL_to_D_aux1>

#proof[
  Same as for @lem:embedding_SPL_to_S_aux1.
]

#lemma[
  The following rule is admissible in $GentzenD$.
  $
    #prooftree(rule($Sigma^Vis, Box Gamma seq(ell) Box A$, $Sigma^Vis, Gamma, Box A seq(1) A$))
  $
] <lem:embedding_DPL_to_D_aux2>

#proof[
  As in @lem:embedding_SPL_to_S_aux2, we first obtain $Box Sigma^Vis, Box Gamma seq(1) Box A$ by $RWL(1, 1)$ and $RBoxGL(1, 1)$.
  Since every formula in this sequent is boxed, we can lift it to $Box Sigma^Vis, Box Gamma seq(ell) Box A$ by applying $RLift(1, 2)$ and $RLift(2, 3)$ as appropriate.
  Then, by @lem:embedding_DPL_to_D_aux1 and $RCut(ell, ell)$, we successively replace the elements of $Box Sigma^Vis$ and obtain $Sigma^Vis, Box Gamma seq(ell) Box A$.
]

The following two lemmas explain the shape of the rule $RLift(2, 3)$ of $GentzenDPL$:
in $GentzenD$, the formulas $p^Vis = p and Box p$ and $Box p$ are interderivable at level $2$, while at level $3$ only the direction from $p^Vis$ to $Box p$ survives.
Hence a boxed variable $Box p$ occurring in the antecedent of an application of $RLift(2, 3)$ of $GentzenD$ corresponds, on the propositional side, to the bare propositional variable $p$.

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
      noted([(@lem:GentzenD_axioms)], $Box p seq(2) Box p$),
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
        noted([(@lem:GentzenD_axioms)], $Box p seq(3) Box p$),
      ),
    ))
  $
]

#remark[
  We do not allow propositional variables to occur in the succedent of the rule $RLift(2, 3)$ of $GentzenDPL$.
  As we will see in the proof of @lem:embedding_DPL_to_D, such an extension would require $GentzenD proves Box p seq(3) p^Vis$, and hence $GentzenD proves Box p seq(3) p$, which is not available since the reflection $Box A -> A$ is not a theorem of $LogicD$.
  This asymmetry does not cause any problem in the converse direction either: the succedent of the conclusion of an application of $RLift(2, 3)$ of $GentzenD$ consists of boxed formulas, and the boxed formulas among the translations are exactly those of implications, so no propositional variable arises there.
] <rem:Lift_no_succedent_variables>

#lemma[
  If $GentzenDPL proves Gamma seq(ell) Delta$, then $GentzenD proves Gamma^Vis seq(ell) Delta^Vis$.
] <lem:embedding_DPL_to_D>

#proof[
  We show by induction on the height of the proof-tree.
  We consider the case of $RLift(2, 3)$; the remaining cases are handled exactly as in @lem:embedding_SPL_to_S, using Lemmas #thmnumber(<lem:embedding_DPL_to_D_aux1>) and #thmnumber(<lem:embedding_DPL_to_D_aux2>) in place of Lemmas #thmnumber(<lem:embedding_SPL_to_S_aux1>) and #thmnumber(<lem:embedding_SPL_to_S_aux2>).

  *Case* $RLift(2, 3)$:
  Suppose the rule we now wish to consider has the following form, where $Phi$ is a set of propositional variables.
  $
    #prooftree(rule(
      name: $RLift(2, 3)$,
      $GentzenDPL provesh(h) {A_i -> B_i : 0 <= i < n}, Phi seq(3) {C_j -> D_j : 0 <= j < m}$,
      $GentzenDPL provesh(h-1) {A_i -> B_i : 0 <= i < n}, Phi seq(2) {C_j -> D_j : 0 <= j < m}$,
    ))
  $
  By the induction hypothesis, we have $GentzenD proves {Box(A^Vis_i -> B^Vis_i) : 0 <= i < n}, Phi^Vis seq(2) {Box(C^Vis_j -> D^Vis_j) : 0 <= j < m}$.
  Here every formula on both sides other than $Phi^Vis$ is boxed, whereas the formulas $p^Vis = p and Box p$ for $p in Phi$ are not, so the rule $RLift(2, 3)$ of $GentzenD$ is not applicable yet.
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

As in @sect:Embedding_GentzenSPL_GentzenS, the converse direction is proved in the following strengthened form.

#lemma[
  Let $Gamma, Delta$ be sets of propositional formulas and let $Phi_1, Phi_2, Psi$ be sets of propositional variables.
  If $GentzenD proves Gamma^Vis, Phi_1, Box Phi_2 seq(ell) Psi, Delta^Vis$,
  then $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(ell) Psi, Delta$.
] <lem:embedding_D_to_DPL_general>

#proof[
  As in @lem:embedding_S_to_SPL_general, no formula in the assumed sequent is an implication, and hence the last rule of a proof-tree of the assumed sequent is neither $RImpL(ell, ell)$ nor $RImpR(ell, ell)$; note that this also excludes these rules at level $3$.
  We show by induction on the height of the proof-tree.
  All the cases other than $RLift(2, 3)$ are handled exactly as in @lem:embedding_S_to_SPL_general.

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

#lemma[
  If $GentzenD proves Gamma^Vis seq(ell) Delta^Vis$, then $GentzenDPL proves Gamma seq(ell) Delta$.
] <lem:embedding_D_to_DPL>

#proof[
  Take $Phi_1 = Phi_2 = Psi = emptyset$ in @lem:embedding_D_to_DPL_general.
]

#theorem[
  $GentzenDPL proves Gamma seq(ell) Delta$ iff $GentzenD proves Gamma^Vis seq(ell) Delta^Vis$.
] <thm:embedding_GentzenDPL_GentzenD>

#proof[
  This follows by combining @lem:embedding_DPL_to_D and @lem:embedding_D_to_DPL.
]

Combining @thm:embedding_GentzenDPL_GentzenD with the properties of $GentzenD$ (Propositions #thmnumber(<prop:GentzenD_provability>) and #thmnumber(<prop:GentzenD_cut_elimination>)), we immediately obtain the following corollaries.

#corollary[
  $LogicDPL proves A$ iff $LogicD proves A^Vis$ for every $A in FmlPL$.
] <cor:embedding_GentzenDPL_D>

#corollary[Cut-admissibility of $GentzenDPL$][
  In $GentzenDPL$, the cut rule $RCut(ell, ell)$ is admissible.
] <cor:GentzenDPL_cut_elimination>

We note that the discussion on whether the embedding is purely syntactic is similar to that in @rem:syntacticality_embedding.

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
obtained by slightly modifying the definitions of $GentzenSPL$ and $GentzenDPL$, can also be embedded into $LogicS$ and $LogicD$;
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

As we noted in @rem:syntacticality_embedding,
the embeddability and the cut-admissibility of our systems for $LogicSPL$ and $LogicDPL$ rely
on the cut-admissibility of the sequent calculi for $LogicS$ and $LogicD$,
and the latter is established by semantic arguments, so our results are not purely syntactic.
It is still open to give a constructive cut-elimination algorithm for the sequent calculi $GentzenSPL$ and $GentzenDPL$.
