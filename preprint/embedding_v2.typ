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
There is a level-up rule from $seq(1)$ to $seq(2)$, but not vice versa.
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

/*
This paper is organized as follows.
In @sect:preliminaries, we introduce some notations and definitions that are used throughout the paper and mention some basic facts.
In @sect:GentzenS, we define a sequent calculus $GentzenS$ for $LogicS$
and show some syntactic results from @Kus20 @KK23.
In @sect:GentzenSPL, we define a sequent calculus $GentzenSPL$ for $LogicSPL$.
In @sect:Embedding_GentzenSPL_GentzenS, we show that $GentzenSPL$ can be embedded into $GentzenS$ via the modified Gödel translation.
Additionally, we mention some errors in Petrukhin's proof in @sect:errors_in_petrukhin.
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
  not A :equiv A -> bot, quad top :equiv not bot, quad A and B :equiv not (A -> not B), quad A or B :equiv not A -> B.
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
] <prop:gl_d_s>

The Gödel translation is a well-known embedding of intuitionistic propositional logic into modal logic.

#definition[Gödel translation][
  Gödel translation $(dot)^God : FmlPL -> FmlML$ is defined as follows.
  $
            p^God & equiv Box p \
          bot^God & equiv Box bot \
    (A and B)^God & equiv A^God and B^God \
     (A or B)^God & equiv A^God or B^God \
     (A -> B)^God & equiv Box (A^God -> B^God) \
  $
  For a set $Gamma$ of propositional formulas, we write $Gamma^God$ for the set ${A^God : A in Gamma}$.
] <def:godel>

However, for our purpose, we need another translation, introduced by Visser @Vis81, which we call Visser--Gödel translation.

#definition[Visser--Gödel translation @Vis81][
  Visser--Gödel translation $(dot)^Vis : FmlPL -> FmlML$ is defined as follows.
  $
            p^Vis & equiv p and Box p \
          bot^Vis & equiv bot \
    (A and B)^Vis & equiv A^Vis and B^Vis \
     (A or B)^Vis & equiv A^Vis or B^Vis \
     (A -> B)^Vis & equiv Box (A^Vis -> B^Vis) \
  $
  For a set $Gamma$ of propositional formulas, we write $Gamma^Vis$ for the set ${A^Vis : A in Gamma}$, and $FmlPL^Vis$ for the image ${A^Vis : A in FmlPL}$ of the translation.
] <def:visser>

It is easy to see that $(dot)^Vis$ is injective, that is, $A^Vis equiv B^Vis$ implies $A equiv B$.

#remark[
  Since the connectives $not$, $and$ and $or$ of modal logic are abbreviations defined from $->$ and $bot$, the Visser--Gödel translation is, once the abbreviations are unfolded, different from what its appearance suggests:

  $
            p^Vis & equiv (p -> (Box p -> bot)) -> bot, \
    (A and B)^Vis & equiv (A^Vis -> (B^Vis -> bot)) -> bot, \
     (A or B)^Vis & equiv (A^Vis -> bot) -> B^Vis.
  $

  Thus the translations of propositional variables, conjunctions and disjunctions are implications, and the translations of implications are boxed formulas.
  This point requires particular care when we consider a proof-theoretic embedding.
] <rem:visser_unfolded>

Visser @Vis81 proved the following by means of Kripke semantics.

#proposition[@Vis81[Theorem 5.2]][
  Let $A in FmlPL$. The following are equivalent.
  1. $LogicFPL proves A$.
  2. $LogicGL proves A^Vis$.
  3. $LogicGL proves A^God$.
] <prop:visser_fpl>

As explained in @subsect:main_results, the equivalence of 1 and 2 can also be proved proof-theoretically along the lines of @YS17.

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
Instead, we adopt a slight modification of the sequent calculus for $LogicD$ due to Kashima et al. @KKIM25,
whose restriction to sequents of levels $1$ and $2$ is a sequent calculus for $LogicS$.
In this subsection, we introduce the calculus and state some of its proof-theoretic properties.

#definition[Sequent calculus $GentzenD$][
  Let $Gamma, Delta$ be finite sets of formulas in $FmlML$ and let $level = 1, 2, 3$.
  The expression $Gamma seq(level) Delta$, that is, the pair $(Gamma, Delta)$ together with the level $level$, is called a _sequent_ of level $level$.
  In the context of sequents, we write $A, Gamma$ for ${A} union Gamma$ and $Gamma, Delta$ for $Gamma union Delta$;
  in particular $A, Gamma = Gamma$ when $A in Gamma$, so that contraction is built into the notation.

  The sequent calculus $GentzenD$ for $LogicD$ consists of the following initial sequents and rules, where $level = 1, 2, 3$ is arbitrary unless otherwise stated.

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
  We call $RWk(level, level)$ _weakening_ and $RLift(1, 2)$, $RLift(2, 3)$ the _level-up rules_.
] <def:gentzen_d>

The level of each premise of a rule is at most the level of its conclusion.
Hence a derivation of a sequent of level at most $2$ consists of sequents of level at most $2$ only and contains no application of $RLift(2, 3)$;
the restriction of $GentzenD$ to the levels $1$ and $2$ is a sequent calculus for $LogicS$, and its restriction to the level $1$ is the usual sequent calculus for $LogicGL$ (cf. @SV82).

Note that in @KKIM25 the initial sequents are $A seq(level) A$ for arbitrary formulas $A$, whereas we restrict $RAx(level)$ to propositional variables.
The restriction of the initial sequents to propositional variables is merely a technical modification for the proof-theoretic embedding in the next section;
by the following lemma, $GentzenD$ may be regarded as having the same deductive power as the calculus of @KKIM25.

#lemma[
  For any $A in FmlML$ and $level = 1, 2, 3$, $GentzenD proves A seq(level) A$.
] <lem:gentzen_d_refl>

#proof[
  We show by induction on $A$, uniformly in $level = 1, 2, 3$.
  If $A equiv p$, the claim is $RAx(level)$.
  If $A equiv bot$, apply $RWk(level, level)$ to $RBotL(level)$.
  The case $A equiv B -> C$ is proved by the following derivation:
  $
    #prooftree(rule(name: $RImpR(level, level)$, $B -> C seq(level) B -> C$, rule(
      name: $RImpL(level, level)$,
      $B -> C, B seq(level) C$,
      rule(name: $RWk(level, level)$, $B seq(level) C, B$, ih($B seq(level) B$)),
      rule(name: $RWk(level, level)$, $C, B seq(level) C$, ih($C seq(level) C$)),
    )))
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
  Moreover, when $level = 3$, we apply $RLift(2, 3)$ to $Box B seq(2) Box B$, since both sides consist of boxed formulas, and obtain $Box B seq(3) Box B$.
]

By this lemma, the calculus $GentzenD$ and that of @KKIM25 are equivalent, and hence the following facts established in @KKIM25 hold for $GentzenD$ as well.

#proposition[Provability of $GentzenD$ @KKIM25[Propositions 3.4--3.6, Theorems 4.1, 4.2]][
  Let $Gamma, Delta subset.eq FmlML$ be finite.
  + $GentzenD proves Gamma seq(1) Delta$ iff $LogicGL proves lconj Gamma -> ldisj Delta$.
  + $GentzenD proves Gamma seq(2) Delta$ iff $LogicS proves lconj Gamma -> ldisj Delta$.
  + $GentzenD proves Gamma seq(3) Delta$ iff $LogicD proves lconj Gamma -> ldisj Delta$.
] <prop:gentzen_d_logic>

#proposition[Cut-admissibility of $GentzenD$ @KKIM25[Theorems 4.1, 4.2, 5.4, 5.6, 5.8]][
  The below rule $RCut(level, level)$ is admissible in $GentzenD$.
  $
    #prooftree(rule(
      name: $RCut(level, level)$,
      $Gamma_1, Gamma_2 seq(level) Delta_1, Delta_2$,
      $Gamma_1 seq(level) Delta_1, A$,
      $A, Gamma_2 seq(level) Delta_2$,
    ))
  $
] <prop:gentzen_d_cut>

Note that @KKIM25 proves the cut-elimination in two ways: by a reduction to the syntactic cut-elimination for Kushida's calculus @Kus20, and by a semantic argument.
In what follows, we use $RCut(level, level)$ freely in derivations in $GentzenD$, as an admissible rule.

#lemma[
  For each $level = 1, 2, 3$, the following rules $RAndL(level, level)$, $RAndR(level, level)$, $ROrL(level, level)$ and $ROrR(level, level)$ are derivable in $GentzenD$, that is, their conclusions are derived from their premises by the rules of $GentzenD$.

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
] <lem:gentzen_d_and_or>

#proof[
  Routine, recalling that $A and B equiv (A -> (B -> bot)) -> bot$ and $A or B equiv (A -> bot) -> B$; the derivations use only $RImpL(level, level)$, $RImpR(level, level)$, $RWk(level, level)$ and $RBotL(level)$.
  For instance, $RAndL(level, level)$ is derived as follows.
  $
    #prooftree(rule(
      name: $RImpL(level, level)$,
      $(A -> (B -> bot)) -> bot, Gamma seq(level) Delta$,
      rule(name: $RImpR(level, level)$, $Gamma seq(level) Delta, A -> (B -> bot)$, rule(
        name: $RImpR(level, level)$,
        $A, Gamma seq(level) Delta, B -> bot$,
        rule(name: $RWk(level, level)$, $A, B, Gamma seq(level) Delta, bot$, $A, B, Gamma seq(level) Delta$),
      )),
      rule(name: $RWk(level, level)$, $bot, Gamma seq(level) Delta$, rule(name: $RBotL(level)$, $bot seq(level)$)),
    ))
  $
]

= Embedding

In this section, we define by a sequent calculus the propositional logics $LogicSPL$ and $LogicDPL$, which correspond via the translation $(dot)^Vis$ to $LogicS$ and $LogicD$, respectively.

#definition[Sequent calculus $GentzenDPL$][
  Let $Gamma, Delta$ be finite sets of formulas in $FmlPL$ and let $level = 1, 2, 3$; sequents $Gamma seq(level) Delta$ and the notation $A, Gamma$ are as in @def:gentzen_d.
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
          $Delta_I, Gamma, A -> B, A seq(1) B, Gamma_I colon I subset.eq {0, dots, k - 1}$,
        ))
        where $k >= 0$, $C_0 -> D_0, ..., C_(k - 1) -> D_(k - 1)$ are arbitrary, and we set $Delta_I := {D_j : j in I}$ and $Gamma_I := {C_j : j in.not I}$.
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
] <def:gentzen_dpl>

As in $GentzenD$, a derivation of a sequent of level at most $2$ in $GentzenDPL$ contains no application of $RLift(2, 3)$.

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
] <ex:gentzen_dpl_imp_r>

We now define the logics $LogicSPL$ and $LogicDPL$ as sets of formulas.

#definition[
  We define _Solovay Propositional Logic_ $LogicSPL$ and  _Dzhaparidze Propositional Logic_ $LogicDPL$.
  - $LogicSPL := {A in FmlPL : GentzenDPL proves seq(2) A}$.
  - $LogicDPL := {A in FmlPL : GentzenDPL proves seq(3) A}$.
] <def:spl_dpl>

#lemma[
  For every $A in FmlPL$ and $level = 1, 2, 3$, $GentzenDPL proves A seq(level) A$.
] <lem:gentzen_dpl_refl>

#proof[
  We show the claim by induction on $A$, simultaneously for $level = 1, 2, 3$.
  If $A equiv p$, the claim is $RAx(level)$.
  If $A equiv bot$, apply $RWk(level, level)$ to $RBotL(level)$.
  If $A equiv B and C$, we have the following derivation.
  $
    #prooftree(rule(
      name: $RAndR(level, level)$,
      $B and C seq(level) B and C$,
      rule(
        name: $RAndL(level, level)$,
        $B and C seq(level) B$,
        rule(name: $RWk(level, level)$, $B, C seq(level) B$, ih($B seq(level) B$)),
      ),
      rule(
        name: $RAndL(level, level)$,
        $B and C seq(level) C$,
        rule(name: $RWk(level, level)$, $B, C seq(level) C$, ih($C seq(level) C$)),
      ),
    ))
  $
  If $A equiv B or C$, we have the following derivation.
  $
    #prooftree(rule(
      name: $ROrL(level, level)$,
      $B or C seq(level) B or C$,
      rule(
        name: $ROrR(level, level)$,
        $B seq(level) B or C$,
        rule(name: $RWk(level, level)$, $B seq(level) B, C$, ih($B seq(level) B$)),
      ),
      rule(
        name: $ROrR(level, level)$,
        $C seq(level) B or C$,
        rule(name: $RWk(level, level)$, $C seq(level) B, C$, ih($C seq(level) C$)),
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
  When $level = 2, 3$, we further apply $RLift(1, 2)$, and when $level = 3$ we apply $RLift(2, 3)$ to $B -> C seq(2) B -> C$ with $n = m = 1$ and $Phi = emptyset$, which is applicable since both sides consist of implications.
]

/*
#remark[
  The rule $RImpR(1, 1)$ is the rule $(->)$ of the sequent calculus $sans("LFP")$ for $LogicFPL$ of @IKK01[Section 3], whose sequents are also pairs of finite sets.
  In fact, up to the formulation of weakening, the restriction of $GentzenDPL$ to the level $1$ is $sans("LFP")$ with its initial sequents $A seq(1) A$ restricted to propositional variables, which by @lem:gentzen_dpl_refl does not change the derivable sequents.
  Hence, by the correspondence between $sans("LFP")$ and $LogicFPL$ in @IKK01[Section 4], $GentzenDPL proves seq(1) A$ iff $LogicFPL proves A$.
] <rem:level_one_fpl>
*/

== Proof-theoretical proof <subsect:main_results>

Our embedding theorem is @thm:iff_visser.
We give a detailed proof of the embedding of $GentzenDPL$ into $GentzenD$ based on the proofs in @YS17 @Pet23.

#lemma[
  For $level = 1, 2, 3$, the following rule $RBoxKFour(1, level)$ is derivable in $GentzenD$.
  $
    #prooftree(rule(name: $RBoxKFour(1, level)$, $Box Gamma seq(level) Box A$, $Box Gamma, Gamma seq(1) A$))
  $
] <lem:box_k4>

#proof[
  For $level = 1$, the claim is proved by the following derivation:
  $
    #prooftree(rule(
      name: $RBoxGL(1, 1)$,
      $Box Gamma seq(1) Box A$,
      rule(name: $RWk(1, 1)$, $Gamma, Box Gamma, Box A seq(1) A$, $Gamma, Box Gamma seq(1) A$),
    ))
  $
  When $level = 2$, we further apply $RLift(1, 2)$, and when $level = 3$ also $RLift(2, 3)$, which is applicable since both the antecedent and the succedent consist of boxed formulas; we obtain $Box Gamma seq(level) Box A$.
]

#lemma[cf. @YS17[Lemma 3]][
  For every $A in FmlPL$ and $level = 1, 2, 3$, $GentzenD proves A^Vis seq(level) Box A^Vis$.
] <lem:persist_visser>

#proof[
  By induction on $A$. The case $A equiv B or C$ is omitted.

  #struct[Case $A equiv p$][
    Here $p^Vis equiv p and Box p$.
    $
      #prooftree(rule(name: $RAndL(level, level)$, $p and Box p seq(level) Box (p and Box p)$, rule(
        name: $RWk(level, level)$,
        $p, Box p seq(level) Box (p and Box p)$,
        rule(name: $RBoxKFour(1, level)$, $Box p seq(level) Box (p and Box p)$, rule(
          name: $RAndR(1, 1)$,
          $Box p, p seq(1) p and Box p$,
          noted([(@lem:gentzen_d_refl, $RWk(1, 1)$)], $Box p, p seq(1) p$),
          noted([(@lem:gentzen_d_refl, $RWk(1, 1)$)], $Box p, p seq(1) Box p$),
        )),
      )))
    $
  ]

  #struct[Case $A equiv bot$][
    Since $bot^Vis equiv bot$, apply $RWk(level, level)$ to $RBotL(level)$.
  ]

  #struct[Case $A equiv B and C$][
    Here $(B and C)^Vis equiv B^Vis and C^Vis$.
    $
      #prooftree(rule(name: $RAndL(level, level)$, $B^Vis and C^Vis seq(level) Box (B^Vis and C^Vis)$, rule(
        name: $RCut(level, level)$,
        $B^Vis, C^Vis seq(level) Box (B^Vis and C^Vis)$,
        rule(
          name: $RAndR(level, level)$,
          $B^Vis, C^Vis seq(level) Box B^Vis and Box C^Vis$,
          rule(name: $RWk(level, level)$, $B^Vis, C^Vis seq(level) Box B^Vis$, ih($B^Vis seq(level) Box B^Vis$)),
          rule(name: $RWk(level, level)$, $B^Vis, C^Vis seq(level) Box C^Vis$, ih($C^Vis seq(level) Box C^Vis$)),
        ),
        rule(name: $RAndL(level, level)$, $Box B^Vis and Box C^Vis seq(level) Box (B^Vis and C^Vis)$, rule(
          name: $RBoxKFour(1, level)$,
          $Box B^Vis, Box C^Vis seq(level) Box (B^Vis and C^Vis)$,
          rule(
            name: $RAndR(1, 1)$,
            $B^Vis, C^Vis, Box B^Vis, Box C^Vis seq(1) B^Vis and C^Vis$,
            noted([(@lem:gentzen_d_refl, $RWk(1, 1)$)], $B^Vis, C^Vis, Box B^Vis, Box C^Vis seq(1) B^Vis$),
            noted([(@lem:gentzen_d_refl, $RWk(1, 1)$)], $B^Vis, C^Vis, Box B^Vis, Box C^Vis seq(1) C^Vis$),
          ),
        )),
      )))
    $
  ]

  #struct[Case $A equiv B -> C$][
    Here $(B -> C)^Vis equiv Box (B^Vis -> C^Vis)$.
    $
      #prooftree(rule(name: $RBoxKFour(1, level)$, $Box (B^Vis -> C^Vis) seq(level) Box Box (B^Vis -> C^Vis)$, noted(
        [(@lem:gentzen_d_refl, $RWk(1, 1)$)],
        $Box (B^Vis -> C^Vis), B^Vis -> C^Vis seq(1) Box (B^Vis -> C^Vis)$,
      )))
    $
  ]

]

#lemma[cf. @YS17[Lemma 5]][
  Let $Sigma subset.eq FmlPL$ and $Gamma subset.eq FmlML$ be finite sets.
  The following rule is admissible in $GentzenD$.
  $
    #prooftree(rule($Sigma^Vis, Box Gamma seq(1) Box A$, $Sigma^Vis, Gamma, Box A seq(1) A$))
  $
] <lem:box_gl_visser>

#proof[
  First, we obtain $Box Sigma^Vis, Box Gamma seq(1) Box A$ as follows, by an instance of $RBoxGL(1, 1)$ in which the set of unboxed formulas is $Sigma^Vis union Gamma$.
  $
    #prooftree(rule(name: $RBoxGL(1, 1)$, $Box Sigma^Vis, Box Gamma seq(1) Box A$, rule(
      name: $RWk(1, 1)$,
      $Box Sigma^Vis, Sigma^Vis, Box Gamma, Gamma, Box A seq(1) A$,
      $Sigma^Vis, Gamma, Box A seq(1) A$,
    )))
  $
  Now, by @lem:persist_visser, for every $B in Sigma$ we have $GentzenD proves B^Vis seq(1) Box B^Vis$.
  Hence, applying $RCut(1, 1)$ with the cut formula $Box B^Vis$ for each $B in Sigma$ in turn, we replace the elements of $Box Sigma^Vis$ in the antecedent by those of $Sigma^Vis$ and obtain $Sigma^Vis, Box Gamma seq(1) Box A$.
]

#lemma[
  For every $p in PropVar$, $GentzenD proves Box p seq(2) p^Vis$.
] <lem:visser_atom_of_box>

#proof[
  Follows from:
  $
    #prooftree(rule(
      name: $RAndR(2, 2)$,
      $Box p seq(2) p and Box p$,
      rule(name: $RBoxL(2, 2)$, $Box p seq(2) p$, rule(name: $RAx(2)$, $p seq(2) p$)),
      noted([(@lem:gentzen_d_refl)], $Box p seq(2) Box p$),
    ))
  $
]

#lemma[
  For every $p in PropVar$, $GentzenD proves p^Vis seq(3) Box p$.
] <lem:box_of_visser_atom>

#proof[
  Follows from:
  $
    #prooftree(rule(name: $RAndL(3, 3)$, $p and Box p seq(3) Box p$, rule(
      name: $RWk(3, 3)$,
      $p, Box p seq(3) Box p$,
      noted([(@lem:gentzen_d_refl)], $Box p seq(3) Box p$),
    )))
  $
]

We are now ready to prove one direction of @thm:iff_visser.

#lemma[cf. @Pet23[Lemma 4]][
  If $GentzenDPL proves Gamma seq(level) Delta$, then $GentzenD proves Gamma^Vis seq(level) Delta^Vis$.
] <lem:visser>

#proof[
  By induction on a derivation of $Gamma seq(level) Delta$ in $GentzenDPL$, distinguishing cases by the last rule.

  #struct[Case $RAx(level)$, $RBotL(level)$][
    The initial sequent $p seq(level) p$ is mapped to $p^Vis seq(level) p^Vis$, which is derivable by @lem:gentzen_d_refl.
    Since $bot^Vis equiv bot$, the initial sequent $bot seq(level)$ is mapped to itself.
  ]

  #struct[Case $RWk(level, level)$][
    Here $Gamma subset.eq Gamma'$ and $Delta subset.eq Delta'$, so $Gamma^Vis subset.eq Gamma'^Vis$ and $Delta^Vis subset.eq Delta'^Vis$.
    #rewrite(
      prooftree(rule(name: $RWk(level, level)$, $Gamma' seq(level) Delta'$, $Gamma seq(level) Delta$)),
      prooftree(rule(
        name: $RWk(level, level)$,
        $Gamma'^Vis seq(level) Delta'^Vis$,
        ih($Gamma^Vis seq(level) Delta^Vis$),
      )),
    )
  ]

  #struct[Case $RLift(1, 2)$][
    Follows from:
    #rewrite(
      prooftree(rule(name: $RLift(1, 2)$, $Gamma seq(2) Delta$, $Gamma seq(1) Delta$)),
      prooftree(rule(name: $RLift(1, 2)$, $Gamma^Vis seq(2) Delta^Vis$, ih($Gamma^Vis seq(1) Delta^Vis$))),
    )
  ]

  #struct[Case $RAndL(level, level)$, $RAndR(level, level)$, $ROrL(level, level)$, $ROrR(level, level)$][
    Since $(A and B)^Vis equiv A^Vis and B^Vis$ and $(A or B)^Vis equiv A^Vis or B^Vis$, apply the corresponding rule of @lem:gentzen_d_and_or to the sequents given by the induction hypothesis.
  ]

  #struct[Case $RImpR(1, 1)$][
    Fix $k$, and suppose that the last rule has the following form, where $Delta_I$ and $Gamma_I$ are as in @def:gentzen_dpl.
    $
      #prooftree(rule(
        name: $RImpR(1, 1)$,
        $Sigma, {C_j -> D_j : j < k} seq(1) A -> B$,
        $Delta_I, Sigma, A -> B, A seq(1) B, Gamma_I colon I subset.eq {0, dots, k - 1}$,
      ))
    $
    Since $(A -> B)^Vis equiv Box (A^Vis -> B^Vis)$, the induction hypothesis gives, for every $I subset.eq {0, dots, k - 1}$,
    $
      GentzenD proves Delta_I^Vis, Sigma^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis, Gamma_I^Vis.
    $
    Combining these $2^k$ sequents with $2^k - 1$ appropriate applications of $RImpL(1, 1)$, we obtain
    $
      GentzenD proves {C_j^Vis -> D_j^Vis : j < k}, Sigma^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis.
    $
    Here we illustrate the case $k = 2$ below; this example is easy to generalize to arbitrary $k$.
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
    The rest is carried out as follows, where @lem:box_gl_visser is applied with $Gamma := {C_j^Vis -> D_j^Vis : j < k}$.
    $
      #prooftree(rule(
        name: [@lem:box_gl_visser],
        $Sigma^Vis, {Box (C_j^Vis -> D_j^Vis) : j < k} seq(1) Box (A^Vis -> B^Vis)$,
        rule(
          name: $RImpR(1, 1)$,
          $Sigma^Vis, {C_j^Vis -> D_j^Vis : j < k}, Box (A^Vis -> B^Vis) seq(1) A^Vis -> B^Vis$,
          $Sigma^Vis, {C_j^Vis -> D_j^Vis : j < k}, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$,
        ),
      ))
    $
    The conclusion is nothing but $Sigma^Vis, {C_j -> D_j : j < k}^Vis seq(1) (A -> B)^Vis$.
  ]

  #struct[Case $RImpL(2, 2)$][
    Follows from:
    #rewrite(
      prooftree(rule(
        name: $RImpL(2, 2)$,
        $A -> B, Gamma seq(2) Delta$,
        $Gamma seq(2) Delta, A$,
        $B, Gamma seq(2) Delta$,
      )),
      prooftree(rule(name: $RBoxL(2, 2)$, $Box (A^Vis -> B^Vis), Gamma^Vis seq(2) Delta^Vis$, rule(
        name: $RImpL(2, 2)$,
        $A^Vis -> B^Vis, Gamma^Vis seq(2) Delta^Vis$,
        ih($Gamma^Vis seq(2) Delta^Vis, A^Vis$),
        ih($B^Vis, Gamma^Vis seq(2) Delta^Vis$),
      ))),
    )
    The conclusion is nothing but $(A -> B)^Vis, Gamma^Vis seq(2) Delta^Vis$.
  ]

  #struct[Case $RLift(2, 3)$][
    Suppose that the last rule has the following form, where $Phi$ is a finite set of propositional variables.
    $
      #prooftree(rule(
        name: $RLift(2, 3)$,
        ${A_i -> B_i : i < n}, Phi seq(3) {C_j -> D_j : j < m}$,
        ${A_i -> B_i : i < n}, Phi seq(2) {C_j -> D_j : j < m}$,
      ))
    $
    By the induction hypothesis, we have $GentzenD proves {Box(A^Vis_i -> B^Vis_i) : i < n}, Phi^Vis seq(2) {Box(C^Vis_j -> D^Vis_j) : j < m}$.
    Here every formula on both sides other than $Phi^Vis$ is boxed, but the formulas $p^Vis equiv p and Box p$ for $p in Phi$ are not, so the rule $RLift(2, 3)$ is not applicable yet.
    First, using @lem:visser_atom_of_box and $RCut(2, 2)$ with the cut formula $p^Vis$, we successively replace each $p^Vis$ in the antecedent by $Box p$, and obtain
    $
      GentzenD proves {Box(A^Vis_i -> B^Vis_i) : i < n}, Box Phi seq(2) {Box(C^Vis_j -> D^Vis_j) : j < m}.
    $
    Since every formula in this sequent is boxed, the rule $RLift(2, 3)$ of $GentzenD$ applies and yields
    $
      GentzenD proves {Box(A^Vis_i -> B^Vis_i) : i < n}, Box Phi seq(3) {Box(C^Vis_j -> D^Vis_j) : j < m}.
    $
    Finally, using @lem:box_of_visser_atom and $RCut(3, 3)$ with the cut formula $Box p$, we successively replace each $Box p$ back by $p^Vis$, and obtain
    $
      GentzenD proves {Box(A^Vis_i -> B^Vis_i) : i < n}, Phi^Vis seq(3) {Box(C^Vis_j -> D^Vis_j) : j < m},
    $
    which is nothing but ${A_i -> B_i : i < n}^Vis, Phi^Vis seq(3) {C_j -> D_j : j < m}^Vis$.
  ]

]

Next, we prove the converse direction in a strengthened form, following the strategy of @YS17[Lemma 7].
The proof proceeds by induction on the height of a derivation in $GentzenD$ of a sequent built from translations, propositional variables and boxed propositional variables, distinguishing cases by the last rule.
By @rem:visser_unfolded, the principal formula of the last rule may be a translation $p^Vis$, $(B and C)^Vis$ or $(B or C)^Vis$, which is an implication;
the premise then contains a formula such as $B^Vis -> (C^Vis -> bot)$ that is not a translation.
We remove such formulas by the height-preserving rules $Inv(RImpL(level, level))$ and $Inv(RImpR(level, level))$ so as to return to a sequent of the required form.
We first collect the syntactic properties of translations that this requires.

#lemma[
  Denote $FmlPL^Vis := {A^Vis : A in FmlPL}$.
  + No element of $FmlPL^Vis$ is a propositional variable or of the form $Box p$ with $p in PropVar$.
  + An element of $FmlPL^Vis$ that is an implication is of the form $p^Vis$, $(B and C)^Vis$ or $(B or C)^Vis$, and one that is of the form $Box E$ is of the form $(B -> C)^Vis$.
  + $A^Vis equiv bot$ iff $A equiv bot$.
  + The antecedent of every implication in $FmlPL^Vis$ is an implication.
] <lem:visser_shape>

#proof[
  All claims can be shown from the following table of the form of $A^Vis$ according to the form of $A$ (see @rem:visser_unfolded).
  - If $A equiv p$, then $p^Vis equiv (p -> (Box p -> bot)) -> bot$, an implication with the antecedent $p -> (Box p -> bot)$.
  - If $A equiv bot$, then $bot^Vis equiv bot$.
  - If $A equiv B and C$, then $(B and C)^Vis equiv (B^Vis -> (C^Vis -> bot)) -> bot$, an implication with the antecedent $B^Vis -> (C^Vis -> bot)$.
  - If $A equiv B or C$, then $(B or C)^Vis equiv (B^Vis -> bot) -> C^Vis$, an implication with the antecedent $B^Vis -> bot$.
  - If $A equiv B -> C$, then $(B -> C)^Vis equiv Box (B^Vis -> C^Vis)$.
  In particular, the antecedents $p -> (Box p -> bot)$, $B^Vis -> (C^Vis -> bot)$ and $B^Vis -> bot$ of the implications among translations are themselves implications.
]

#lemma[
  There is no $A in FmlML$ such that both $A in FmlPL^Vis$ and $A -> bot in FmlPL^Vis$.
] <lem:visser_neg>

#proof[
  We show by induction of $A$.
  By contrast, suppose $A in FmlPL^Vis$ and $A -> bot in FmlPL^Vis$.
  Since $A -> bot$ is an implication in $FmlPL^Vis$ whose consequent is $bot$, by the table in the proof of @lem:visser_shape it is $p^Vis$, $(B and C)^Vis$ or $(B or bot)^Vis$ for some $p$, $B$, $C$.
  - If $A -> bot equiv p^Vis$, then $A equiv p -> (Box p -> bot)$, whose antecedent $p$ is not an implication; so $A in.not FmlPL^Vis$ by @lem:visser_shape, a contradiction.
  - If $A -> bot equiv (B and C)^Vis$, then $A equiv B^Vis -> (C^Vis -> bot)$. Since $A$ is an implication in $FmlPL^Vis$ whose consequent is not $bot$, the table gives $A equiv (D or E)^Vis equiv (D^Vis -> bot) -> E^Vis$ for some $D$, $E$, so $D^Vis -> bot equiv B^Vis$.
    Then $A' :equiv D^Vis$ is a proper subformula of $A$ with $A' in FmlPL^Vis$ and $A' -> bot in FmlPL^Vis$.
    so it can violate by the induction hypothesis.
  - If $A -> bot equiv (B or bot)^Vis$, then $A equiv B^Vis -> bot$. Then $A' :equiv B^Vis$ is a proper subformula of $A$ with $A' in FmlPL^Vis$ and $A' -> bot equiv A in FmlPL^Vis$, contradicting the induction hypothesis.
]

Before the proof, we introduce the definition of the height of a derivation with some modification.

#definition[
  The _height_ $height(cal(D))$ of a derivation $cal(D)$ in $GentzenD$ is the maximum, over all branches of $cal(D)$, of the number of applications of rules _other than_ $RWk(level, level)$.
  We write $GentzenD provesh(h) Gamma seq(level) Delta$ if $Gamma seq(level) Delta$ has a derivation in $GentzenD$ of height at most $h$ in this sense.
] <def:height>

Under this definition, weakening does not increase the height:
if $Gamma subset.eq Gamma'$, $Delta subset.eq Delta'$ and $GentzenD provesh(h) Gamma seq(level) Delta$, then $GentzenD provesh(h) Gamma' seq(level) Delta'$.
In the derivations displayed below, a node $GentzenD provesh(h) S$ indicates that the subderivation ending there has height at most $h$.
この修正の意義は，高さを保った逆転補題などにおいてinduction hypothesisを利用した場合，principle formulaの一部分が欠ける場合があり，そのとき $RWk(level, level)$ によって補填する必要がある．その場合高さがincrementされると所望の高さ以下の結論が得られないためである．

#lemma[
  If $GentzenD provesh(h) Gamma seq(level) Delta$, then $GentzenD provesh(h) Gamma seq(level) Delta without {bot}$.
] <lem:erase_bot>

#proof[
  By structural induction on a derivation $cal(D)$ of $Gamma seq(level) Delta$, we show that there is a derivation of $Gamma seq(level) Delta without {bot}$ whose height is at most $h := height(cal(D))$.
  We distinguish cases by the last rule of $cal(D)$.

  #struct[Case $RAx(level)$, $RBotL(level)$, $RBoxGL(1, 1)$, $RLift(2, 3)$][
    The succedent consists only of propositional variables and boxed formulas, so it does not contain $bot$ and there is nothing to do.
  ]

  #struct[Case $RWk(level, level)$][
    Here $Gamma_0 subset.eq Gamma$ and $Delta_0 subset.eq Delta$, and the premise also has height at most $h$; note that $Delta_0 without {bot} subset.eq Delta without {bot}$.
    #rewrite(
      prooftree(rule(
        name: $RWk(level, level)$,
        $GentzenD provesh(h) Gamma seq(level) Delta$,
        $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
      )),
      prooftree(rule(
        name: $RWk(level, level)$,
        $GentzenD provesh(h) Gamma seq(level) Delta without {bot}$,
        ih($GentzenD provesh(h) Gamma_0 seq(level) Delta_0 without {bot}$),
      )),
    )
  ]

  #struct[Case $RBoxL(2, 2)$][
    Here $Gamma = Gamma' union {Box C}$.
    #rewrite(
      prooftree(rule(
        name: $RBoxL(2, 2)$,
        $GentzenD provesh(h) Box C, Gamma' seq(2) Delta$,
        $GentzenD provesh(h-1) C, Gamma' seq(2) Delta$,
      )),
      prooftree(rule(
        name: $RBoxL(2, 2)$,
        $GentzenD provesh(h) Box C, Gamma' seq(2) Delta without {bot}$,
        ih($GentzenD provesh(h-1) C, Gamma' seq(2) Delta without {bot}$),
      )),
    )
  ]

  #struct[Case $RLift(1, 2)$][
    #rewrite(
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) Gamma seq(2) Delta$,
        $GentzenD provesh(h-1) Gamma seq(1) Delta$,
      )),
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) Gamma seq(2) Delta without {bot}$,
        ih($GentzenD provesh(h-1) Gamma seq(1) Delta without {bot}$),
      )),
    )
  ]

  #struct[Case $RImpL(level, level)$][
    Here $Gamma = Gamma' union {C -> D}$.
    - If $C equiv.not bot$, we apply the induction hypothesis to both premises and then $RImpL(level, level)$.
      #rewrite(
        prooftree(rule(
          name: $RImpL(level, level)$,
          $GentzenD provesh(h) C -> D, Gamma' seq(level) Delta$,
          $GentzenD provesh(h-1) Gamma' seq(level) Delta, C$,
          $GentzenD provesh(h-1) D, Gamma' seq(level) Delta$,
        )),
        prooftree(rule(
          name: $RImpL(level, level)$,
          $GentzenD provesh(h) C -> D, Gamma' seq(level) Delta without {bot}$,
          ih($GentzenD provesh(h-1) Gamma' seq(level) Delta without {bot}, C$),
          ih($GentzenD provesh(h-1) D, Gamma' seq(level) Delta without {bot}$),
        )),
      )
    - If $C equiv bot$, the induction hypothesis applied to the left premise removes $C$, and we add $C -> D$ by weakening, which does not increase the height.
      #rewrite(
        prooftree(rule(
          name: $RImpL(level, level)$,
          $GentzenD provesh(h) bot -> D, Gamma' seq(level) Delta$,
          $GentzenD provesh(h-1) Gamma' seq(level) Delta, bot$,
          $GentzenD provesh(h-1) D, Gamma' seq(level) Delta$,
        )),
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h-1) bot -> D, Gamma' seq(level) Delta without {bot}$,
          ih($GentzenD provesh(h-1) Gamma' seq(level) Delta without {bot}$),
        )),
      )
  ]

  #struct[Case $RImpR(level, level)$][
    Here $Delta = Delta' union {C -> D}$.
    - If $D equiv.not bot$, we apply the induction hypothesis to the premise and then $RImpR(level, level)$.
      #rewrite(
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta', C -> D$,
          $GentzenD provesh(h-1) C, Gamma seq(level) Delta', D$,
        )),
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta' without {bot}, C -> D$,
          ih($GentzenD provesh(h-1) C, Gamma seq(level) Delta' without {bot}, D$),
        )),
      )
    - If $D equiv bot$, the induction hypothesis removes $D$, so we add it back by weakening before applying $RImpR(level, level)$.
      #rewrite(
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta', C -> bot$,
          $GentzenD provesh(h-1) C, Gamma seq(level) Delta', bot$,
        )),
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta' without {bot}, C -> bot$,
          rule(
            name: $RWk(level, level)$,
            $GentzenD provesh(h-1) C, Gamma seq(level) Delta' without {bot}, bot$,
            ih($GentzenD provesh(h-1) C, Gamma seq(level) Delta' without {bot}$),
          ),
        )),
      )
      先ほど説明したように，ここで $RWk(level, level)$ の適用で高さが増えてしまう定義にすると $h$ 以下の結論導出が得られない，ということを注意しておこう．
  ]

]

We now show that the inversion rules for implication are height-preservingly admissible with respect to this height.

#lemma[Inversion rules $Inv(RImpL(level, level))$ of $GentzenD$][
  In $GentzenD$ the inversion rules $Inv(RImpL(level, level))$ are height-preservingly admissible.
  That is, for every $h$, if $A -> B in.not Gamma$ then the following hold.
  #side-by-side(
    prooftree(rule(
      name: $Inv(RImpL(level, level))$,
      $GentzenD provesh(h) Gamma seq(level) Delta, A$,
      $GentzenD provesh(h) A -> B, Gamma seq(level) Delta$,
    )),
    prooftree(rule(
      name: $Inv(RImpL(level, level))$,
      $GentzenD provesh(h) B, Gamma seq(level) Delta$,
      $GentzenD provesh(h) A -> B, Gamma seq(level) Delta$,
    )),
  )
  We call the two conclusions the _left_ and the _right_ one.
] <lem:inv_imp_l>

#proof[
  We show the following by induction on a derivation $cal(D)$ of $Gamma seq(level) Delta$ with $A -> B in Gamma$:
  there are derivations of $Gamma without {A -> B} seq(level) Delta, A$ and of $B, Gamma without {A -> B} seq(level) Delta$ whose heights are at most the height of $cal(D)$.
  We distinguish cases by the last rule of $cal(D)$.
  We display only the derivations for the left conclusion.

  #struct[Case $RAx(level)$, $RBotL(level)$, $RBoxGL(1, 1)$, $RLift(2, 3)$][
    The antecedent of the conclusion consists only of propositional variables, $bot$ and formulas of the form $Box C$, so it does not contain $A -> B$.
    Thus this case does not occur.
  ]

  #struct[Case $RWk(level, level)$][
    Here $Gamma_0 subset.eq Gamma$ and $Delta_0 subset.eq Delta$, and the premise also has height at most $h$.
    - If $A -> B in Gamma_0$, we apply the induction hypothesis to the premise and then $RWk(level, level)$.
      #rewrite(
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta$,
          $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
        )),
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) Gamma without {A -> B} seq(level) Delta, A$,
          ih($GentzenD provesh(h) Gamma_0 without {A -> B} seq(level) Delta_0, A$),
        )),
      )
    - If $A -> B in.not Gamma_0$, then $Gamma_0 subset.eq Gamma without {A -> B}$, and $RWk(level, level)$ applied to the premise itself gives the required sequent.
      #rewrite(
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta$,
          $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
        )),
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) Gamma without {A -> B} seq(level) Delta, A$,
          $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
        )),
      )
  ]

  #struct[Case $RImpL(level, level)$][
    The last rule is of the form below, where $Gamma = Gamma' union {C -> D}$.
    $
      #prooftree(rule(
        name: $RImpL(level, level)$,
        $GentzenD provesh(h) C -> D, Gamma' seq(level) Delta$,
        $GentzenD provesh(h-1) Gamma' seq(level) Delta, C$,
        $GentzenD provesh(h-1) D, Gamma' seq(level) Delta$,
      ))
    $
    - Suppose $C -> D equiv A -> B$.
      - If $A -> B in.not Gamma'$, then $Gamma' = Gamma without {A -> B}$, and the two premises $GentzenD provesh(h-1) Gamma without {A -> B} seq(level) Delta, A$ and $GentzenD provesh(h-1) B, Gamma without {A -> B} seq(level) Delta$ are the desired sequents.
      - If $A -> B in Gamma'$, then $Gamma' without {A -> B} = Gamma without {A -> B}$, and we apply the induction hypothesis for the left conclusion to the left premise, and that for the right conclusion to the right premise.
        $
          #ih($GentzenD provesh(h-1) Gamma without {A -> B} seq(level) Delta, A$) quad quad #ih($GentzenD provesh(h-1) B, Gamma without {A -> B} seq(level) Delta$)
        $
    - Suppose $C -> D equiv.not A -> B$ and $D equiv.not A -> B$.
      Then $A -> B in Gamma'$ and $Gamma without {A -> B} = (Gamma' without {A -> B}) union {C -> D}$.
      $
        #prooftree(rule(
          name: $RImpL(level, level)$,
          $GentzenD provesh(h) C -> D, Gamma' without {A -> B} seq(level) Delta, A$,
          ih($GentzenD provesh(h-1) Gamma' without {A -> B} seq(level) Delta, C, A$),
          ih($GentzenD provesh(h-1) D, Gamma' without {A -> B} seq(level) Delta, A$),
        ))
      $
    - Suppose $C -> D equiv.not A -> B$ and $D equiv A -> B$.
      Then $A -> B in Gamma'$, and the induction hypothesis applied to the right premise removes $D$, so we add $C -> D$ by weakening.
      $
        #prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h-1) C -> D, Gamma' without {A -> B} seq(level) Delta, A$,
          ih($GentzenD provesh(h-1) Gamma' without {A -> B} seq(level) Delta, A$),
        ))
      $
  ]

  #struct[Case $RImpR(level, level)$][
    Here $Delta = Delta' union {C -> D}$.
    - If $C equiv.not A -> B$, we apply the induction hypothesis to the premise and then $RImpR(level, level)$.
      #rewrite(
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta', C -> D$,
          $GentzenD provesh(h-1) C, Gamma seq(level) Delta', D$,
        )),
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) Gamma without {A -> B} seq(level) Delta', C -> D, A$,
          ih($GentzenD provesh(h-1) C, Gamma without {A -> B} seq(level) Delta', D, A$),
        )),
      )
    - If $C equiv A -> B$, the induction hypothesis removes $C$, so we add it back by weakening before applying $RImpR(level, level)$.
      #rewrite(
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta', (A -> B) -> D$,
          $GentzenD provesh(h-1) A -> B, Gamma seq(level) Delta', D$,
        )),
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) Gamma without {A -> B} seq(level) Delta', (A -> B) -> D, A$,
          rule(
            name: $RWk(level, level)$,
            $GentzenD provesh(h-1) A -> B, Gamma without {A -> B} seq(level) Delta', D, A$,
            ih($GentzenD provesh(h-1) Gamma without {A -> B} seq(level) Delta', D, A$),
          ),
        )),
      )
  ]

  #struct[Case $RBoxL(2, 2)$][
    Here $Gamma = Gamma' union {Box C}$; since $Box C equiv.not A -> B$, we have $A -> B in Gamma'$.
    - If $C equiv.not A -> B$, we apply the induction hypothesis to the premise and then $RBoxL(2, 2)$.
      #rewrite(
        prooftree(rule(
          name: $RBoxL(2, 2)$,
          $GentzenD provesh(h) Box C, Gamma' seq(2) Delta$,
          $GentzenD provesh(h-1) C, Gamma' seq(2) Delta$,
        )),
        prooftree(rule(
          name: $RBoxL(2, 2)$,
          $GentzenD provesh(h) Box C, Gamma' without {A -> B} seq(2) Delta, A$,
          ih($GentzenD provesh(h-1) C, Gamma' without {A -> B} seq(2) Delta, A$),
        )),
      )
    - If $C equiv A -> B$, the induction hypothesis removes $C$, so we add $Box C$ by weakening.
      #rewrite(
        prooftree(rule(
          name: $RBoxL(2, 2)$,
          $GentzenD provesh(h) Box C, Gamma' seq(2) Delta$,
          $GentzenD provesh(h-1) C, Gamma' seq(2) Delta$,
        )),
        prooftree(rule(
          name: $RWk(2, 2)$,
          $GentzenD provesh(h-1) Box C, Gamma' without {A -> B} seq(2) Delta, A$,
          ih($GentzenD provesh(h-1) Gamma' without {A -> B} seq(2) Delta, A$),
        )),
      )
  ]

  #struct[Case $RLift(1, 2)$][
    #rewrite(
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) Gamma seq(2) Delta$,
        $GentzenD provesh(h-1) Gamma seq(1) Delta$,
      )),
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) Gamma without {A -> B} seq(2) Delta, A$,
        ih($GentzenD provesh(h-1) Gamma without {A -> B} seq(1) Delta, A$),
      )),
    )
  ]

  The construction for the right conclusion is similar.

]

#lemma[Inversion rule $Inv(RImpR(level, level))$ of $GentzenD$][
  In $GentzenD$ the inversion rule $Inv(RImpR(level, level))$ is height-preservingly admissible.
  That is, for every $h$, if $A -> B in.not Delta$ then the following holds.
  $
    #prooftree(rule(
      name: $Inv(RImpR(level, level))$,
      $GentzenD provesh(h) A, Gamma seq(level) Delta, B$,
      $GentzenD provesh(h) Gamma seq(level) Delta, A -> B$,
    ))
  $
] <lem:inv_imp_r>

#proof[
  We show the following by induction on a derivation $cal(D)$ of $Gamma seq(level) Delta$ with $A -> B in Delta$:
  there is a derivation of $A, Gamma seq(level) Delta without {A -> B}, B$ whose height is at most $height(cal(D))$.
  Since $A -> B in.not Delta$ in the statement, the lemma follows.
  Let $h := height(cal(D))$; we distinguish cases by the last rule of $cal(D)$, with the same conventions as in the proof of @lem:inv_imp_l.

  #struct[Case $RAx(level)$, $RBotL(level)$, $RBoxGL(1, 1)$, $RLift(2, 3)$][
    The succedent of the conclusion consists only of propositional variables and formulas of the form $Box C$, so it does not contain $A -> B$.
    Thus this case does not occur.
  ]

  #struct[Case $RWk(level, level)$][
    Here $Gamma_0 subset.eq Gamma$ and $Delta_0 subset.eq Delta$, and the premise also has height at most $h$.
    - If $A -> B in Delta_0$, we apply the induction hypothesis to the premise and then $RWk(level, level)$.
      #rewrite(
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta$,
          $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
        )),
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) A, Gamma seq(level) Delta without {A -> B}, B$,
          ih($GentzenD provesh(h) A, Gamma_0 seq(level) Delta_0 without {A -> B}, B$),
        )),
      )
    - If $A -> B in.not Delta_0$, then $Delta_0 subset.eq Delta without {A -> B}$, and $RWk(level, level)$ applied to the premise itself gives the required sequent.
      #rewrite(
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta$,
          $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
        )),
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) A, Gamma seq(level) Delta without {A -> B}, B$,
          $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
        )),
      )
  ]

  #struct[Case $RImpL(level, level)$][
    The last rule is of the form below, where $Gamma = Gamma' union {C -> D}$.
    $
      #prooftree(rule(
        name: $RImpL(level, level)$,
        $GentzenD provesh(h) C -> D, Gamma' seq(level) Delta$,
        $GentzenD provesh(h-1) Gamma' seq(level) Delta, C$,
        $GentzenD provesh(h-1) D, Gamma' seq(level) Delta$,
      ))
    $
    - If $C equiv.not A -> B$, we apply the induction hypothesis to both premises and then $RImpL(level, level)$.
      #wide(prooftree(rule(
        name: $RImpL(level, level)$,
        $GentzenD provesh(h) A, C -> D, Gamma' seq(level) Delta without {A -> B}, B$,
        ih($GentzenD provesh(h-1) A, Gamma' seq(level) Delta without {A -> B}, C, B$),
        ih($GentzenD provesh(h-1) A, D, Gamma' seq(level) Delta without {A -> B}, B$),
      )))
    - If $C equiv A -> B$, the induction hypothesis applied to the left premise removes $C$, so we add $C -> D$ by weakening.
      $
        #prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h-1) A, C -> D, Gamma' seq(level) Delta without {A -> B}, B$,
          ih($GentzenD provesh(h-1) A, Gamma' seq(level) Delta without {A -> B}, B$),
        ))
      $
  ]

  #struct[Case $RImpR(level, level)$][
    Here $Delta = Delta' union {C -> D}$.
    - Suppose $C -> D equiv A -> B$.
      - If $A -> B in.not Delta'$, then $Delta' = Delta without {A -> B}$, and the premise is the desired derivation.
        #rewrite(
          prooftree(rule(
            name: $RImpR(level, level)$,
            $GentzenD provesh(h) Gamma seq(level) Delta', C -> D$,
            $GentzenD provesh(h-1) C, Gamma seq(level) Delta', D$,
          )),
          $GentzenD provesh(h-1) A, Gamma seq(level) Delta without {A -> B}, B$,
        )
      - If $A -> B in Delta'$, then $Delta' without {A -> B} = Delta without {A -> B}$, and we apply the induction hypothesis to the premise; note that $B equiv.not A -> B$.
        #rewrite(
          prooftree(rule(
            name: $RImpR(level, level)$,
            $GentzenD provesh(h) Gamma seq(level) Delta', C -> D$,
            $GentzenD provesh(h-1) C, Gamma seq(level) Delta', D$,
          )),
          ih($GentzenD provesh(h-1) A, Gamma seq(level) Delta without {A -> B}, B$),
        )
    - Suppose $C -> D equiv.not A -> B$ and $D equiv.not A -> B$.
      Then $A -> B in Delta'$ and $Delta without {A -> B} = (Delta' without {A -> B}) union {C -> D}$, and we apply the induction hypothesis to the premise and then $RImpR(level, level)$.
      #rewrite(
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta', C -> D$,
          $GentzenD provesh(h-1) C, Gamma seq(level) Delta', D$,
        )),
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) A, Gamma seq(level) Delta' without {A -> B}, C -> D, B$,
          ih($GentzenD provesh(h-1) A, C, Gamma seq(level) Delta' without {A -> B}, D, B$),
        )),
      )
    - Suppose $C -> D equiv.not A -> B$ and $D equiv A -> B$.
      Then $A -> B in Delta'$, and the induction hypothesis removes $D$, so we add it back by weakening before applying $RImpR(level, level)$.
      #rewrite(
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta', C -> D$,
          $GentzenD provesh(h-1) C, Gamma seq(level) Delta', D$,
        )),
        prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) A, Gamma seq(level) Delta' without {A -> B}, C -> (A -> B), B$,
          rule(
            name: $RWk(level, level)$,
            $GentzenD provesh(h-1) A, C, Gamma seq(level) Delta' without {A -> B}, A -> B, B$,
            ih($GentzenD provesh(h-1) A, C, Gamma seq(level) Delta' without {A -> B}, B$),
          ),
        )),
      )
  ]

  #struct[Case $RBoxL(2, 2)$][
    Here $Gamma = Gamma' union {Box C}$.
    #rewrite(
      prooftree(rule(
        name: $RBoxL(2, 2)$,
        $GentzenD provesh(h) Box C, Gamma' seq(2) Delta$,
        $GentzenD provesh(h-1) C, Gamma' seq(2) Delta$,
      )),
      prooftree(rule(
        name: $RBoxL(2, 2)$,
        $GentzenD provesh(h) A, Box C, Gamma' seq(2) Delta without {A -> B}, B$,
        ih($GentzenD provesh(h-1) A, C, Gamma' seq(2) Delta without {A -> B}, B$),
      )),
    )
  ]

  #struct[Case $RLift(1, 2)$][
    #rewrite(
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) Gamma seq(2) Delta$,
        $GentzenD provesh(h-1) Gamma seq(1) Delta$,
      )),
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) A, Gamma seq(2) Delta without {A -> B}, B$,
        ih($GentzenD provesh(h-1) A, Gamma seq(1) Delta without {A -> B}, B$),
      )),
    )
  ]

]

The converse direction is proved for sequents in which propositional variables and boxed propositional variables may occur besides translations, since the premise of $RBoxL(2, 2)$ with the principal formula $Box p$ contains $p$.

#lemma[cf. @Pet23[Lemma 5]][
  Let $Gamma, Delta subset.eq FmlPL$ and $Phi_1, Phi_2, Psi subset.eq PropVar$ be finite sets.
  If $GentzenD proves Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis$,
  then $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta$.
] <lem:of_visser>

#proof[
  Let $cal(D)$ be a derivation of the $GentzenD proves Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis$ and $h := height(cal(D))$.
  We prove the claim by induction along the lexicographic order on the pairs $(height(cal(D)), mrm("rules")(cal(D)))$, where $mrm("rules")(cal(D))$ is the number of applications of rules in $cal(D)$, distinguishing cases by the last rule of $cal(D)$.
  The induction hypothesis applies to every derivation of height at most $height(cal(D)) - 1$, including those that are not subderivations of $cal(D)$, such as the ones produced by $Inv(RImpL(level, level))$ and $Inv(RImpR(level, level))$.
  It also applies to the premise of the last rule if that rule is $RWk(level, level)$, since the premise may have the same height as $cal(D)$ but has fewer applications of rules.

  The statement is generalized over $Gamma, Delta, Phi_1, Phi_2$ and $Psi$:
  in each case below, a sequent obtained from the premises of the last rule is re-decomposed into the form $Gamma'^Vis, Phi'_1, Box Phi'_2 seq(level) Psi', Delta'^Vis$, with components different from those of the conclusion, and the induction hypothesis is applied to this decomposition.
  In each case we display the last rule, the derivations in $GentzenD$ obtained from its premises by $Inv(RImpL(level, level))$ and $Inv(RImpR(level, level))$, and the derivation in $GentzenDPL$ built from the sequents given by the induction hypothesis (I.H.).

  We first note the following.
  By @lem:visser_shape, the three sets $Gamma^Vis$, $Phi_1$ and $Box Phi_2$ are pairwise disjoint, as are $Psi$ and $Delta^Vis$;
  an element of $Gamma^Vis$ or $Delta^Vis$ that is an implication is $A^Vis$ for a propositional variable, a conjunction or a disjunction $A$, and one that is boxed is $(A -> B)^Vis$ for an implication $A -> B$.
  Since $GentzenDPL$ has $RWk(level, level)$, it suffices to derive in $GentzenDPL$ a sequent whose antecedent is a subset of $Gamma, Phi_1, Phi_2$ and whose succedent is a subset of $Psi, Delta$.
  Since $RWk(level, level)$ of $GentzenD$ does not increase the height, a sequent of height at most $h - 1$ may be weakened before the induction hypothesis is applied to it; we use this tacitly.

  #struct[Case $RAx(level)$][
    The sequent is $p seq(level) p$.
    By @lem:visser_shape, $p in Phi_1$ and $p in Psi$, and $RAx(level)$ of $GentzenDPL$ gives $p seq(level) p$.
  ]

  #struct[Case $RBotL(level)$][
    The sequent is $bot seq(level)$.
    By @lem:visser_shape, $bot in Gamma$, and $RBotL(level)$ of $GentzenDPL$ gives $bot seq(level)$.
  ]

  #struct[Case $RWk(level, level)$][
    The antecedent of the premise is a subset of $Gamma^Vis, Phi_1, Box Phi_2$, hence of the form $Gamma'^Vis, Phi'_1, Box Phi'_2$ with $Gamma' subset.eq Gamma$, $Phi'_1 subset.eq Phi_1$ and $Phi'_2 subset.eq Phi_2$;
    similarly its succedent is of the form $Psi', Delta'^Vis$ with $Psi' subset.eq Psi$ and $Delta' subset.eq Delta$.
    We apply the induction hypothesis to the premise.
    #rewrite(
      prooftree(rule(
        name: $RWk(level, level)$,
        $GentzenD provesh(h) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis$,
        $GentzenD provesh(h) Gamma'^Vis, Phi'_1, Box Phi'_2 seq(level) Psi', Delta'^Vis$,
      )),
      prooftree(rule(
        name: $RWk(level, level)$,
        $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta$,
        ih($GentzenDPL proves Gamma', Phi'_1, Phi'_2 seq(level) Psi', Delta'$),
      )),
    )
  ]

  #struct[Case $RLift(1, 2)$][
    Follows from:
    #rewrite(
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) Gamma^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
        $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(1) Psi, Delta^Vis$,
      )),
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(2) Psi, Delta$,
        ih($GentzenDPL proves Gamma, Phi_1, Phi_2 seq(1) Psi, Delta$),
      )),
    )
  ]

  #struct[Case $RImpL(level, level)$][
    The principal formula is an implication in the antecedent, hence it is $A^Vis$ for some $A in Gamma$ that is $A equiv p, B and C, B or C$.
    The last rule is an instance of $RImpL(level, level)$ with the principal formula $A^Vis$.
    By @lem:visser_shape, there is $Gamma' subset.eq Gamma$ with $Gamma = Gamma' union {A}$ such that the rest of the antecedent is $Gamma'^Vis, Phi_1, Box Phi_2$ (possibly $A in Gamma'$).
    By @rem:visser_unfolded, $A^Vis equiv D -> E$ with
    - $A equiv p$: $D equiv p -> (Box p -> bot)$ and $E equiv bot$;
    - $A equiv B and C$: $D equiv B^Vis -> (C^Vis -> bot)$ and $E equiv bot$;
    - $A equiv B or C$: $D equiv B^Vis -> bot$ and $E equiv C^Vis$.
    Hence, the last rule is of the following form.
    #wide(prooftree(rule(
      name: $RImpL(level, level)$,
      $GentzenD provesh(h) A^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis$,
      $GentzenD provesh(h-1) Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis, D$,
      $GentzenD provesh(h-1) E, Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis$,
    )))
    In each case below we invert the left premise to remove the formulas that are not translations, apply the induction hypothesis to the resulting sequents, and obtain the desired sequent by the rule of $GentzenDPL$ that corresponds to $A$.
    - $A equiv p$:
      The antecedents of $p -> (Box p -> bot)$ and $Box p -> bot$ are not implications, so these formulas are not in $FmlPL^Vis$ by @lem:visser_shape, hence not in $Psi, Delta^Vis$, and $Inv(RImpR(level, level))$ applies to them.
      From the left premise we obtain the following, where @lem:visser_shape gives $(Psi union Delta^Vis union {bot}) without {bot} = Psi, (Delta without {bot})^Vis$.
      #wide(prooftree(rule(
        name: [@lem:erase_bot],
        $GentzenD provesh(h-1) p, Box p, Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta without {bot})^Vis$,
        rule(
          name: $Inv(RImpR(level, level))$,
          $GentzenD provesh(h-1) p, Box p, Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis, bot$,
          rule(
            name: $Inv(RImpR(level, level))$,
            $GentzenD provesh(h-1) p, Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis, Box p -> bot$,
            $GentzenD provesh(h-1) Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis, p -> (Box p -> bot)$,
          ),
        ),
      )))
      Regarding the antecedent of the conclusion as $Gamma'^Vis, (Phi_1 union {p}), Box (Phi_2 union {p})$, we apply the induction hypothesis.
      Since $Gamma' union {p} = Gamma$, we obtain the desired sequent as follows.
      $
        #prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta$,
          ih($GentzenDPL proves Gamma', p, Phi_1, Phi_2 seq(level) Psi, Delta without {bot}$),
        ))
      $
    - $A equiv B and C$:
      The formula $B^Vis -> (C^Vis -> bot)$ is not in $FmlPL^Vis$: its consequent is not $bot$, so if it were, by the table in the proof of @lem:visser_shape it would be $(B' or C')^Vis equiv (B'^Vis -> bot) -> C'^Vis$ with $C'^Vis equiv C^Vis -> bot$, and $C^Vis$ and $C^Vis -> bot$ would both be in $FmlPL^Vis$, contradicting @lem:visser_neg.
      Also $C^Vis -> bot$ is not in $FmlPL^Vis$ by @lem:visser_neg, since $C^Vis in FmlPL^Vis$.
      Hence neither of them belongs to $Psi, Delta^Vis$, and $Inv(RImpR(level, level))$ applies to them.
      From the left premise we obtain the following.
      #wide(prooftree(rule(
        name: [@lem:erase_bot],
        $GentzenD provesh(h-1) B^Vis, C^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta without {bot})^Vis$,
        rule(
          name: $Inv(RImpR(level, level))$,
          $GentzenD provesh(h-1) B^Vis, C^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis, bot$,
          rule(
            name: $Inv(RImpR(level, level))$,
            $GentzenD provesh(h-1) B^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis, C^Vis -> bot$,
            $GentzenD provesh(h-1) Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis, B^Vis -> (C^Vis -> bot)$,
          ),
        ),
      )))
      Regarding the antecedent of the conclusion as $(Gamma' union {B, C})^Vis, Phi_1, Box Phi_2$, we apply the induction hypothesis and obtain the desired sequent as follows.
      $
        #prooftree(rule(name: $RWk(level, level)$, $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta$, rule(
          name: $RAndL(level, level)$,
          $GentzenDPL proves B and C, Gamma', Phi_1, Phi_2 seq(level) Psi, Delta without {bot}$,
          ih($GentzenDPL proves B, C, Gamma', Phi_1, Phi_2 seq(level) Psi, Delta without {bot}$),
        )))
      $
    - $A equiv B or C$:
      The formula $B^Vis -> bot$ is not in $FmlPL^Vis$ by @lem:visser_neg, since $B^Vis in FmlPL^Vis$.
      So, it does not belong to $Psi, Delta^Vis$ and $Inv(RImpR(level, level))$ can be applied to it from the left premise, we obtain the following.
      #wide(prooftree(rule(
        name: [@lem:erase_bot],
        $GentzenD provesh(h-1) B^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta without {bot})^Vis$,
        rule(
          name: $Inv(RImpR(level, level))$,
          $GentzenD provesh(h-1) B^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis, bot$,
          $GentzenD provesh(h-1) Gamma'^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis, B^Vis -> bot$,
        ),
      )))
      We apply the induction hypothesis to this conclusion and to the right premise, regarding their antecedents as $(Gamma' union {B})^Vis, Phi_1, Box Phi_2$ and $(Gamma' union {C})^Vis, Phi_1, Box Phi_2$, and obtain the desired sequent as follows.
      $
        #prooftree(rule(name: $RWk(level, level)$, $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta$, rule(
          name: $ROrL(level, level)$,
          $GentzenDPL proves B or C, Gamma', Phi_1, Phi_2 seq(level) Psi, Delta$,
          rule(
            name: $RWk(level, level)$,
            $GentzenDPL proves B, Gamma', Phi_1, Phi_2 seq(level) Psi, Delta$,
            ih($GentzenDPL proves B, Gamma', Phi_1, Phi_2 seq(level) Psi, Delta without {bot}$),
          ),
          ih($GentzenDPL proves C, Gamma', Phi_1, Phi_2 seq(level) Psi, Delta$),
        )))
      $
  ]

  #struct[Case $RImpR(level, level)$][
    The principal formula is an implication in the succedent, hence it is $A^Vis$ for some $A in Delta$ that is a $A equiv p, B and C, B or C$.
    // 主論理式は後件にある含意なので，Δ のある元 A（命題変数，連言，選言のいずれか）によって A^V と書ける．
    The last rule is an instance of $RImpR(level, level)$ with the principal formula $A^Vis$.
    // 最後の規則は主論理式 A^V をもつ (→R) の適用である．
    By @lem:visser_shape, there is $Delta' subset.eq Delta$ with $Delta = Delta' union {A}$ such that the rest of the succedent is $Psi, Delta'^Vis$ (possibly $A in Delta'$).
    // 補題より，Δ' ⊆ Δ かつ Δ = Δ' ∪ {A} を満たす Δ' で，後件の残りが Ψ, Δ'^V となるものがある（A ∈ Δ' でもよい）．
    The formulas inverted below are the same as in the case $RImpL(level, level)$, which are implications not in $FmlPL^Vis$ (see there), hence they do not belong to $Gamma^Vis, Phi_1, Box Phi_2$, so $Inv(RImpL(level, level))$ and $Inv(RImpR(level, level))$ apply; we use only the left conclusion of $Inv(RImpL(level, level))$ except where stated.
    // 以下で反転する論理式は (→L) の場合と同じで，いずれも FmlPL^V に属さない含意である（そちらを参照）．
    // よって Γ^V, Φ₁, □Φ₂ に属さず，Inv(→L) と Inv(→R) が適用できる．特に断らない限り，Inv(→L) では左の結論のみを使う．
    By @rem:visser_unfolded, $A^Vis equiv D -> E$ with
    - $A equiv p$: $D equiv p -> (Box p -> bot)$ and $E equiv bot$;
    - $A equiv B and C$: $D equiv B^Vis -> (C^Vis -> bot)$ and $E equiv bot$;
    - $A equiv B or C$: $D equiv B^Vis -> bot$ and $E equiv C^Vis$.
    Hence the last rule is of the following form.
    #wide(prooftree(rule(
      name: $RImpR(level, level)$,
      $GentzenD provesh(h) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, A^Vis$,
      $GentzenD provesh(h-1) D, Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, E$,
    )))
    In each case below we invert the premise so as to remove the formulas that are not translations, apply the induction hypothesis to the resulting sequents, and obtain the desired sequent by the rule of $GentzenDPL$ that corresponds to $A$.
    - $A equiv p$:
      From the premise we obtain the following.
      #wide(prooftree(rule(
        name: [@lem:erase_bot],
        $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, p, (Delta' without {bot})^Vis$,
        rule(
          name: $Inv(RImpL(level, level))$,
          $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot, p$,
          $GentzenD provesh(h-1) p -> (Box p -> bot), Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot$,
        ),
      )))
      Regarding the succedent of the conclusion as $(Psi union {p}), (Delta' without {bot})^Vis$, we apply the induction hypothesis.
      Since $Delta' union {p} = Delta$, we obtain the desired sequent as follows.
      $
        #prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta$,
          ih($GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, p, Delta' without {bot}$),
        ))
      $
    - $A equiv B and C$:
      We first obtain $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta' without {bot})^Vis, B^Vis$ from the premise.
      - If $B equiv.not bot$:
        #wide(prooftree(rule(
          name: [@lem:erase_bot],
          $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta' without {bot})^Vis, B^Vis$,
          rule(
            name: $Inv(RImpL(level, level))$,
            $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot, B^Vis$,
            $GentzenD provesh(h-1) B^Vis -> (C^Vis -> bot), Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot$,
          ),
        )))
      - If $B equiv bot$, then $B^Vis equiv bot$, so @lem:erase_bot removes $B^Vis$, and we add it back by $RWk(level, level)$.
        #wide(prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta' without {bot})^Vis, B^Vis$,
          rule(
            name: [@lem:erase_bot],
            $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta' without {bot})^Vis$,
            rule(
              name: $Inv(RImpL(level, level))$,
              $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot, B^Vis$,
              $GentzenD provesh(h-1) B^Vis -> (C^Vis -> bot), Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot$,
            ),
          ),
        )))
      Next we obtain $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta' without {bot})^Vis, C^Vis$ from the premise, using the right conclusion of $Inv(RImpL(level, level))$ first.
      - If $C equiv.not bot$:
        #wide(prooftree(rule(
          name: [@lem:erase_bot],
          $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta' without {bot})^Vis, C^Vis$,
          rule(
            name: $Inv(RImpL(level, level))$,
            $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot, C^Vis$,
            rule(
              name: $Inv(RImpL(level, level))$,
              $GentzenD provesh(h-1) C^Vis -> bot, Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot$,
              $GentzenD provesh(h-1) B^Vis -> (C^Vis -> bot), Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot$,
            ),
          ),
        )))
      - If $C equiv bot$, then $C^Vis equiv bot$, so @lem:erase_bot removes $C^Vis$, and we add it back by $RWk(level, level)$.
        #wide(prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta' without {bot})^Vis, C^Vis$,
          rule(
            name: [@lem:erase_bot],
            $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, (Delta' without {bot})^Vis$,
            rule(
              name: $Inv(RImpL(level, level))$,
              $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot, C^Vis$,
              rule(
                name: $Inv(RImpL(level, level))$,
                $GentzenD provesh(h-1) C^Vis -> bot, Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot$,
                $GentzenD provesh(h-1) B^Vis -> (C^Vis -> bot), Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, bot$,
              ),
            ),
          ),
        )))
      Regarding the succedents of the two sequents obtained as $Psi, ((Delta' without {bot}) union {B})^Vis$ and $Psi, ((Delta' without {bot}) union {C})^Vis$, we apply the induction hypothesis and obtain the desired sequent as follows.
      $
        #prooftree(rule(name: $RWk(level, level)$, $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta$, rule(
          name: $RAndR(level, level)$,
          $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta' without {bot}, B and C$,
          ih($GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta' without {bot}, B$),
          ih($GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta' without {bot}, C$),
        )))
      $
    - $A equiv B or C$:
      From the premise we obtain the following.
      #wide(prooftree(rule(
        name: $Inv(RImpL(level, level))$,
        $GentzenD provesh(h-1) Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, C^Vis, B^Vis$,
        $GentzenD provesh(h-1) B^Vis -> bot, Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta'^Vis, C^Vis$,
      )))
      Regarding the succedent of the conclusion as $Psi, (Delta' union {B, C})^Vis$, we apply the induction hypothesis and obtain the desired sequent as follows.
      $
        #prooftree(rule(name: $RWk(level, level)$, $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta$, rule(
          name: $ROrR(level, level)$,
          $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta', B or C$,
          ih($GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta', B, C$),
        )))
      $
  ]

  #struct[Case $RBoxGL(1, 1)$][
    Here $level = 1$, the antecedent consists of boxed formulas, and the succedent is a single boxed formula.
    Hence $Phi_1 = Psi = emptyset$, every element of $Gamma$ and $Delta$ is an implication by @lem:visser_shape, and $Delta$ is a singleton since $(dot)^Vis$ is injective.
    Write $Gamma = {C_j -> D_j : j < k}$ with the $C_j -> D_j$ pairwise distinct ($k >= 0$) and $Delta = {A -> B}$.
    Since $(A -> B)^Vis equiv Box (A^Vis -> B^Vis)$, the last rule is the following, where the set of unboxed formulas in the premise is ${C_j^Vis -> D_j^Vis : j < k}, Phi_2$.
    #wide(prooftree(rule(
      name: $RBoxGL(1, 1)$,
      $GentzenD provesh(h) Gamma^Vis, Box Phi_2 seq(1) (A -> B)^Vis$,
      $GentzenD provesh(h-1) Gamma^Vis, Box Phi_2, {C_j^Vis -> D_j^Vis : j < k}, Phi_2, (A -> B)^Vis seq(1) A^Vis -> B^Vis$,
    )))
    Fix $I subset.eq {0, dots, k - 1}$, and let $Delta_I := {D_j : j in I}$ and $Gamma_I := {C_j : j in.not I}$ as in @def:gentzen_dpl.
    We first invert $A^Vis -> B^Vis$ by $Inv(RImpR(1, 1))$, and then invert $C_j^Vis -> D_j^Vis$ for $j = 0, dots, k - 1$ in turn by $Inv(RImpL(1, 1))$, using the right conclusion if $j in I$ and the left conclusion if $j in.not I$.
    #wide(prooftree(rule(
      name: [$Inv(RImpL(1, 1))$, $k$ times],
      $GentzenD provesh(h-1) Delta_I^Vis, A^Vis, Gamma^Vis, Phi_2, Box Phi_2, (A -> B)^Vis seq(1) B^Vis, Gamma_I^Vis$,
      rule(
        name: $Inv(RImpR(1, 1))$,
        $GentzenD provesh(h-1) A^Vis, Gamma^Vis, Box Phi_2, {C_j^Vis -> D_j^Vis : j < k}, Phi_2, (A -> B)^Vis seq(1) B^Vis$,
        $GentzenD provesh(h-1) Gamma^Vis, Box Phi_2, {C_j^Vis -> D_j^Vis : j < k}, Phi_2, (A -> B)^Vis seq(1) A^Vis -> B^Vis$,
      ),
    )))
    These applications of $Inv(RImpR(1, 1))$ and $Inv(RImpL(1, 1))$ are legitimate, since each inverted formula is distinct from the other formulas on its side:
    $A^Vis$ and the $D_j^Vis$ belong to $FmlPL^Vis$, whereas $C_j^Vis -> D_j^Vis$ does not: if $D_j equiv bot$, it is $C_j^Vis -> bot$ with $C_j^Vis in FmlPL^Vis$, which is not in $FmlPL^Vis$ by @lem:visser_neg; otherwise its consequent is not $bot$, so if it were in $FmlPL^Vis$, by the table in the proof of @lem:visser_shape it would be $(E or F)^Vis equiv (E^Vis -> bot) -> F^Vis$ with $E^Vis -> bot equiv C_j^Vis$, and $E^Vis$ and $E^Vis -> bot$ would both be in $FmlPL^Vis$, contradicting @lem:visser_neg;
    $Phi_2$ consists of propositional variables, and $Gamma^Vis$, $Box Phi_2$ and $(A -> B)^Vis$ consist of boxed formulas;
    and $C_i^Vis -> D_i^Vis equiv.not C_j^Vis -> D_j^Vis$ for $i eq.not j$, since otherwise $C_i equiv C_j$ and $D_i equiv D_j$ by the injectivity of $(dot)^Vis$.
    Regarding the antecedent of the resulting sequent as $(Delta_I union {A} union Gamma union {A -> B})^Vis, Phi_2, Box Phi_2$ and its succedent as $(Gamma_I union {B})^Vis$, we apply the induction hypothesis and obtain, for every $I subset.eq {0, dots, k - 1}$,
    $
      GentzenDPL proves Delta_I, Gamma, Phi_2, A -> B, A seq(1) B, Gamma_I.
    $
    These $2^k$ sequents are the premises of $RImpR(1, 1)$ of $GentzenDPL$ with the context $Gamma union Phi_2$ and the implications $C_0 -> D_0, dots, C_(k - 1) -> D_(k - 1)$, whose conclusion is $Gamma union Phi_2, {C_j -> D_j : j < k} seq(1) A -> B$, that is, $Gamma, Phi_2 seq(1) Delta$; this is the desired sequent since $Phi_1 = Psi = emptyset$.
    $
      #prooftree(rule(
        name: $RImpR(1, 1)$,
        $GentzenDPL proves Gamma, Phi_2 seq(1) A -> B$,
        ih($GentzenDPL proves Delta_I, Gamma, Phi_2, A -> B, A seq(1) B, Gamma_I colon I subset.eq {0, dots, k - 1}$),
      ))
    $
  ]

  #struct[Case $RBoxL(2, 2)$][
    Here $level = 2$, and by @lem:visser_shape the principal formula is either $Box q$ for some $q in Phi_2$, or $(A -> B)^Vis equiv Box (A^Vis -> B^Vis)$ for some $A -> B in Gamma$.
    - If the principal formula is $Box q$ for some $q in Phi_2$: let $Phi'_2$ be as $Phi'_2 union {q} = Phi_2$.
      Regarding the antecedent of the premise as $Gamma^Vis, (Phi_1 union {q}), Box Phi'_2$, we apply the induction hypothesis and obtain the desired sequent.
      #rewrite(
        prooftree(rule(
          name: $RBoxL(2, 2)$,
          $GentzenD provesh(h) Box q, Gamma^Vis, Phi_1, Box Phi'_2 seq(2) Psi, Delta^Vis$,
          $GentzenD provesh(h-1) q, Gamma^Vis, Phi_1, Box Phi'_2 seq(2) Psi, Delta^Vis$,
        )),
        prooftree(rule(
          name: $RWk(2, 2)$,
          $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(2) Psi, Delta$,
          ih($GentzenDPL proves Gamma, q, Phi_1, Phi'_2 seq(2) Psi, Delta$),
        )),
      )
    - If the principal formula is $(A -> B)^Vis$ for some $A -> B in Gamma$: let $Gamma'$ be as in the case $RImpL(level, level)$, so that $Gamma' union {A -> B} = Gamma$ and the last rule is the following.
      #wide(prooftree(rule(
        name: $RBoxL(2, 2)$,
        $GentzenD provesh(h) (A -> B)^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
        $GentzenD provesh(h-1) A^Vis -> B^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
      )))
      By the same argument as for $C_j^Vis -> D_j^Vis$ in the case $RBoxGL(1, 1)$, $A^Vis -> B^Vis$ does not belong to $FmlPL^Vis$, and hence not to $Gamma'^Vis, Phi_1, Box Phi_2$, so the left and the right conclusion of $Inv(RImpL(2, 2))$ applied to the premise give the following.
      #wide(prooftree(rule(
        name: $Inv(RImpL(2, 2))$,
        $GentzenD provesh(h-1) Gamma'^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis, A^Vis$,
        $GentzenD provesh(h-1) A^Vis -> B^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
      )))
      #wide(prooftree(rule(
        name: $Inv(RImpL(2, 2))$,
        $GentzenD provesh(h-1) B^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
        $GentzenD provesh(h-1) A^Vis -> B^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
      )))
      We apply the induction hypothesis to these two sequents and obtain the desired sequent as follows.
      $
        #prooftree(rule(name: $RWk(2, 2)$, $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(2) Psi, Delta$, rule(
          name: $RImpL(2, 2)$,
          $GentzenDPL proves A -> B, Gamma', Phi_1, Phi_2 seq(2) Psi, Delta$,
          ih($GentzenDPL proves Gamma', Phi_1, Phi_2 seq(2) Psi, Delta, A$),
          ih($GentzenDPL proves B, Gamma', Phi_1, Phi_2 seq(2) Psi, Delta$),
        )))
      $
  ]

  #struct[Case $RLift(2, 3)$][
    Both sides of the conclusion consist of boxed formulas, so $Phi_1 = Psi = emptyset$ and, by @lem:visser_shape, $Gamma$ and $Delta$ consist of implications: $Gamma = {A_i -> B_i : i < n}$ and $Delta = {C_j -> D_j : j < m}$ for some $n, m >= 0$.
    We apply the induction hypothesis to the premise and then $RLift(2, 3)$ of $GentzenDPL$ with $Phi := Phi_2$.
    #rewrite(
      prooftree(rule(
        name: $RLift(2, 3)$,
        $GentzenD provesh(h) Gamma^Vis, Box Phi_2 seq(3) Delta^Vis$,
        $GentzenD provesh(h-1) Gamma^Vis, Box Phi_2 seq(2) Delta^Vis$,
      )),
      prooftree(rule(
        name: $RLift(2, 3)$,
        $GentzenDPL proves Gamma, Phi_2 seq(3) Delta$,
        ih($GentzenDPL proves Gamma, Phi_2 seq(2) Delta$),
      )),
    )
  ]

]

#theorem[cf. @Pet23[Theorem 1]][
  For finite sets $Gamma, Delta subset.eq FmlPL$ and $level = 1, 2, 3$,
  $GentzenDPL proves Gamma seq(level) Delta$ iff $GentzenD proves Gamma^Vis seq(level) Delta^Vis$.
] <thm:iff_visser>

#proof[
  The direction from left to right is @lem:visser.
  The converse is @lem:of_visser with $Phi_1 = Phi_2 = Psi = emptyset$.
]

#corollary[
  Let $A in FmlPL$.

  + $LogicFPL proves A <==> GentzenDPL proves emptyset seq(1) {A} <==> LogicGL proves A^Vis$
  + $LogicSPL proves A <==> GentzenDPL proves emptyset seq(2) {A} <==> LogicS proves A^Vis$
  + $LogicDPL proves A <==> GentzenDPL proves emptyset seq(3) {A} <==> LogicD proves A^Vis$
] <cor:mem_logic_iff>

/*
#proof[
  In each item, the second equivalence holds as follows:
  $GentzenDPL proves emptyset seq(level) {A}$ iff $GentzenD proves emptyset seq(level) {A^Vis}$ by @thm:iff_visser, iff $top -> A^Vis$ is a theorem of $LogicGL$, $LogicS$ or $LogicD$ respectively by @prop:gentzen_d_logic, iff $A^Vis$ is.
  // The first equivalences of items 2 and 3 are the definitions of $LogicSPL$ and $LogicDPL$, and that of item 1 is @rem:level_one_fpl.
]
*/

We mention that proof-theoretic proof of item 1 of <cor:mem_logic_iff> is the equivalence of 1 and 2 in @prop:visser_fpl, which is not treated in @YS17.
Moreover, combining with @prop:gentzen_d_cut, we obtain the cut elimination theorem of $GentzenDPL$.

#corollary[Cut-admissibility of $GentzenDPL$][
  The rule $RCut(level, level)$ is admissible in $GentzenDPL$.
] <cor:gentzen_dpl_cut>

== Errors in Petrukhin's proof <sect:errors_in_petrukhin>

This embedding result is based on Petrukhin @Pet23, but the proof in the original paper appears to contain several errors.
We point them out below.
Throughout this subsection, $GentzenS$ and $GentzenSPL$ denote the calculi used in @Pet23, namely Kushida's sequent calculus for $LogicS$ @Kus20 and Petrukhin's sequent calculus for $LogicSPL$, whose sequents are based on multisets; the names of the rules are adapted to ours.
The issue concerns @Pet23[Lemma 5], which corresponds to @lem:of_visser in the present paper.

#proposition(numbering: none)[@Pet23[Lemma 5]][
  If $GentzenS proves Gamma^Vis, Phi, Box Phi seq(level) Psi, Delta^Vis$, then $GentzenSPL proves Gamma, Phi seq(level) Psi, Delta$.
  Here $Gamma, Delta$ are multisets of formulas and $Phi, Psi$ are multisets of propositional variables.
]

The proof proceeds by induction on the height of the proof-tree of $GentzenS proves Gamma^Vis, Phi, Box Phi seq(level) Psi, Delta^Vis$.
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
This is because $E^Vis -> F^Vis$ never belongs to $Sigma^Vis$ for any $Sigma$, and is of course not a propositional variable, so the premise is not of the form $Gamma^Vis, Phi, Box Phi seq(level) Psi, Delta^Vis$.
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

In this paper, these problems are avoided in @lem:of_visser as follows.
Since our sequents are based on _sets_, contraction is built into the formulation and never needs to be applied explicitly, let alone height-preservingly.
The case where the principal formula of $RBoxL(2, 2)$ is $Box(E^Vis -> F^Vis)$ is handled by the height-preserving inversion $Inv(RImpL(2, 2))$, which returns the premise to the form required by the induction hypothesis; the same device handles the cases of $RImpL(level, level)$ and $RImpR(level, level)$ whose principal formulas are the translations of variables, conjunctions and disjunctions (@rem:visser_unfolded).
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
on the cut-elimination for the sequent calculus for $LogicD$ of @KKIM25 (@prop:gentzen_d_cut); apart from this, the arguments in @subsect:main_results are explicit transformations of derivations.
In @KKIM25 the cut-elimination is obtained by a reduction to the syntactic cut-elimination for Kushida's calculus @Kus20, and also by a semantic argument.
It is still open to give a direct, constructive cut-elimination procedure for the sequent calculi $GentzenDPL$ themselves.
