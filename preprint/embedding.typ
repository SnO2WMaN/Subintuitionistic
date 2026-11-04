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
    Visser showed that his Formal Propositional Logic $LogicFPL$ embeds into the Gödel--Löb provability logic $LogicGL$.
    Analogously, Petrukhin introduced a propositional logic $LogicSPL$ and claimed that it embeds into Solovay's non-normal provability logic $LogicS$.
    In this paper, we point out errors in Petrukhin's proof and give a complete proof of this embedding.
    We then introduce a propositional logic $LogicDPL$ and show that it embeds in the same way into Japaridze's provability logic $LogicD$.
  ],
)

= Introduction

In 1976, Solovay @Sol76 proved the arithmetical completeness theorem, which is a fundamental result in provability logic.
More precisely, he proved that a modal formula is provable in the logic $LogicGL$ if and only if
every arithmetical sentence obtained from it by interpreting the propositional variables as arithmetical sentences
and the modal operator $Box$ as a standard provability predicate $mrm("Pr")_TheoryPA (x)$ of $TheoryPA$ is provable in $TheoryPA$.
As an extension of this result, he also showed that a non-normal extension of $LogicGL$, known as $LogicS$, is arithmetically complete with respect to
true arithmetic $TheoryTA$.
Furthermore, in his thesis @Jap86, Japaridze (also transliterated as Dzhaparidze) discovered a provability logic $LogicD$
that lies strictly between $LogicGL$ and $LogicS$.
The logic $LogicD$ is the provability logic of $TheoryPA$ relative to $TheoryPA + mrm("Rfn")_TheoryPA (Sigma_1)$,
that is, a modal formula is provable in $LogicD$ if and only if
every arithmetical sentence obtained from it by the above interpretation is provable in $TheoryPA + mrm("Rfn")_TheoryPA (Sigma_1)$.
Here, $mrm("Rfn")_TheoryPA (Sigma_1)$ denotes the reflection principle for $Sigma_1$-sentences.
Subsequently, Beklemishev @Bek90 proved the classification theorem for provability logics,
which states that every provability logic must belong to one of four families of logics,
each being an appropriate extension of one of $LogicGL$, $LogicS$ or $LogicD$.
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
is that provability in intuitionistic propositional logic $LogicInt$ can be interpreted as provability in the modal logic $LogicSFour$
via a translation now known as the Gödel translation.
When such a correspondence holds, the modal logic is called a _modal companion_ of the propositional logic
(for instance, $LogicSFour$ is a modal companion of $LogicInt$).
The modal companions of superintuitionistic logics, that is, of logics extending $LogicInt$, are well understood (see @CZ97).
Propositional logics whose modal companions are weaker than or incomparable with $LogicSFour$ have also been studied.
Visser @Vis81 found two propositional logics whose modal companions, via a modified Gödel translation, are $LogicKFour$ and $LogicGL$, respectively,
and named them Basic Propositional Logic $LogicBPL$ and Formal Propositional Logic $LogicFPL$.
Simple sequent calculi for $LogicBPL$ and $LogicFPL$ were proposed by Ishii et al. @IKK01.
Yamasaki and Sano @YS17 modified the sequent calculus of Ishii et al. for $LogicBPL$ into a G3-style sequent calculus
and investigated its proof-theoretic properties.
Moreover, they gave a proof-theoretic embedding of $LogicBPL$ into $LogicKFour$ via a modified Gödel translation.
We also note that Chen @Che21 discussed such an embedding for the logic $Logic("F")$ introduced by Corsi @Cor87, which is weaker than $LogicBPL$ and corresponds to the modal logic $LogicK$.

Petrukhin @Pet23 combined Kushida's idea of two levels of sequents with a sequent calculus for $LogicFPL$
and named the propositional logic defined by the resulting calculus Solovay Propositional Logic $LogicSPL$.
Furthermore, following the method of Yamasaki and Sano, he claimed that a modified Gödel translation embeds his calculus for $LogicSPL$ into Kushida's calculus for $LogicS$,
that is, that $LogicS$ is a modal companion of $LogicSPL$.
However, his proof contains errors that cannot be repaired by straightforward local corrections (see @sect:errors_in_petrukhin).

We now explain the organization and contributions of this paper.
In @sect:preliminaries, we introduce the notation and definitions used in this paper, such as sequent calculi, and state some basic facts.
In @sect:embedding, as the first of our two main results, by refering to the proof-theoretic proofs given in @YS17 and @Pet23 that $LogicKFour$ (resp. $LogicS$) is a modal companion of $LogicBPL$ (resp. $LogicSPL$), define by means of a sequent calculus $GentzenDPL$ a propositional logic $LogicDPL$ that can be embedded into the modal logic $LogicD$, and give a complete and detailed proof of the embedding theorem from scratch.
The result of @Pet23 itself is obtained by restricting the sequent calculus given here appropriately.
Moreover, on the basis of the proof given here, we point out errors in @Pet23.
Next, in @sect:semantics, as the second of our two main results, we define Kripke semantics for $LogicSPL$ and $LogicDPL$.
Using this semantics together with the semantics of $LogicS$ and $LogicD$ given in @KK23 and @KKIM25, we give a semantic proof that $LogicSPL$ and $LogicDPL$ are modal companions of $LogicS$ and $LogicD$, respectively.
Finally, we give some concluding remarks and open problems in @sect:conclusion.

== Acknowledgements

The author would like to thank Kohei Tominaga, Naoyuki Hatanaka, Haruka Kogure and Taishi Kurahashi
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
For more details, see standard textbooks such as @Boo94 @CZ97.

Propositional variables are denoted by lowercase letters $p, q, r, dots$, and the set of all propositional variables is denoted by $PropVar$.
Formulas of propositional logic are built from propositional variables and $bot$ by $and$, $or$ and $->$;
formulas of modal logic are built from propositional variables and $bot$ by $->$ and $Box$.
In both languages, $not$ and $top$ are abbreviations; in modal formulas, $and$ and $or$ are also abbreviations, as follows:

$
  not A :equiv A -> bot, quad top :equiv not bot, quad A and B :equiv not (A -> not B), quad A or B :equiv not A -> B.
$

Formulas of both propositional logic and modal logic are denoted by uppercase letters $A, B, C, dots$.
We write $FmlPL$ for the set of all formulas of propositional logic, and $FmlML$ for the set of all formulas of modal logic.
Uppercase Greek letters $Gamma, Delta, dots$ denote _sets_ of formulas.
For a set $Gamma$ of modal formulas, we write $Box Gamma$ for the set ${Box A : A in Gamma}$.
Moreover, for a finite set $Gamma$, we write $lconj Gamma$ and $ldisj Gamma$ for the conjunction and the disjunction of all elements of $Gamma$,
respectively, where the empty conjunction $lconj emptyset$ and the empty disjunction $ldisj emptyset$ are understood as $top$ and $bot$.

The modal logic $LogicGL$, named after Gödel and Löb, is the smallest normal modal logic containing the axiom $Box (Box A -> A) -> Box A$.
Solovay's modal logic $LogicS$ is the non-normal extension of $LogicGL$ with the axiom $Box A -> A$;
that is, $LogicS$ is the smallest set of formulas that contains all theorems of $LogicGL$ and all instances of $Box A -> A$, and is closed under modus ponens only (but not under necessitation).
Japaridze's modal logic $LogicD$ is the non-normal extension of $LogicGL$ with the axioms $Box (Box A or Box B) -> Box A or Box B$ and $not Box bot$, defined analogously.
The following proposition can be shown by using the semantic tools for $LogicS$ and $LogicD$ developed in @Vis84 @Bek89.

#proposition[
  $LogicGL subset.neq LogicD subset.neq LogicS$.
  That is, $LogicGL proves A$ implies $LogicD proves A$, and $LogicD proves A$ implies $LogicS proves A$, but the converses do not hold.
] <prop:gl_d_s>

The Gödel translation is a well-known embedding of intuitionistic propositional logic into modal logic.

#definition[Gödel translation][
  The Gödel translation $(dot)^God : FmlPL -> FmlML$ is defined as follows.
  $
            p^God & equiv Box p \
          bot^God & equiv Box bot \
    (A and B)^God & equiv A^God and B^God \
     (A or B)^God & equiv A^God or B^God \
     (A -> B)^God & equiv Box (A^God -> B^God) \
  $
  For a set $Gamma$ of propositional formulas, we write $Gamma^God$ for the set ${A^God : A in Gamma}$.
] <def:godel>

Instead of the Gödel translation, we use the following variant introduced by Visser @Vis81, which we call the Visser--Gödel translation.

#definition[Visser--Gödel translation @Vis81][
  The Visser--Gödel translation $(dot)^Vis : FmlPL -> FmlML$ is defined as follows.
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
  Since $not$, $and$ and $or$ are abbreviations in modal formulas, the clauses of @def:visser unfold as follows:

  $
            p^Vis & equiv (p -> (Box p -> bot)) -> bot, \
    (A and B)^Vis & equiv (A^Vis -> (B^Vis -> bot)) -> bot, \
     (A or B)^Vis & equiv (A^Vis -> bot) -> B^Vis.
  $

  Thus $p^Vis$, $(A and B)^Vis$ and $(A or B)^Vis$ are implications, while $(A -> B)^Vis$ is a boxed formula.
  This point requires particular care when we consider a proof-theoretic embedding.
] <rem:visser_unfolded>

Visser @Vis81 proved the following by means of Kripke semantics.

#proposition[@Vis81[Theorem 5.2]][
  Let $A in FmlPL$. The following are equivalent.
  1. $LogicFPL proves A$.
  2. $LogicGL proves A^Vis$.
  3. $LogicGL proves A^God$.
] <prop:visser_fpl>

As we show in @sect:embedding (see @rem:visser_fpl_embedding), the equivalence of items 1 and 2 can also be proved by a proof-theoretic embedding.

== Sequent calculus for modal provability logics

Kushida @Kus20 first introduced a sequent calculus for $LogicS$, but his formulation is somewhat inconvenient for proving our embedding theorem; for example, it is based on multisets in order to give a constructive cut-elimination algorithm.
Therefore, we adopt a slight modification of the sequent calculus for $LogicD$ due to Kashima et al. @KKIM25,
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
Hence a derivation of a sequent of level at most $2$ consists only of sequents of level at most $2$ and contains no application of $RLift(2, 3)$.
This is why the restriction of $GentzenD$ to levels $1$ and $2$ serves as a sequent calculus for $LogicS$ (@prop:gentzen_d_logic); similarly, its restriction to level $1$ is the usual sequent calculus for $LogicGL$ (cf. @SV82).

Note that in @KKIM25 the initial sequents are $A seq(level) A$ for arbitrary formulas $A$, whereas we restrict $RAx(level)$ to propositional variables;
this technical modification is made for the proof-theoretic embedding in @sect:embedding.
By the following lemma, it does not change the derivable sequents.

#lemma[
  For any $A in FmlML$ and $level = 1, 2, 3$, $GentzenD proves A seq(level) A$.
] <lem:gentzen_d_refl>

#proof[
  We show the claim by induction on $A$, simultaneously for $level = 1, 2, 3$.
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

Hence $GentzenD$ derives the same sequents as the calculus of @KKIM25, and the following facts established in @KKIM25 hold for $GentzenD$ as well.

#proposition[Provability of $GentzenD$ @KKIM25[Propositions 3.4--3.6, Theorems 4.1, 4.2]][
  Let $Gamma, Delta subset.eq FmlML$ be finite.
  + $GentzenD proves Gamma seq(1) Delta$ iff $LogicGL proves lconj Gamma -> ldisj Delta$.
  + $GentzenD proves Gamma seq(2) Delta$ iff $LogicS proves lconj Gamma -> ldisj Delta$.
  + $GentzenD proves Gamma seq(3) Delta$ iff $LogicD proves lconj Gamma -> ldisj Delta$.
] <prop:gentzen_d_logic>

#proposition[Cut-admissibility of $GentzenD$ @KKIM25[Theorems 4.1, 4.2, 5.4, 5.6, 5.8]][
  The following rule $RCut(level, level)$ is admissible in $GentzenD$.
  $
    #prooftree(rule(
      name: $RCut(level, level)$,
      $Gamma_1, Gamma_2 seq(level) Delta_1, Delta_2$,
      $Gamma_1 seq(level) Delta_1, A$,
      $A, Gamma_2 seq(level) Delta_2$,
    ))
  $
] <prop:gentzen_d_cut>

Note that @KKIM25 proves cut-elimination in two ways: by a reduction to Kushida's syntactic cut-elimination @Kus20 and by a semantic argument.
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

= Sequent calculus $GentzenDPL$ of logic $LogicDPL$ <sect:seq_DPL>

In this section, we define the propositional logics $LogicSPL$ and $LogicDPL$ by means of a sequent calculus, show that $(dot)^Vis$ embeds them into $LogicS$ and $LogicD$, and additionally discuss the errors in Petrukhin's proof.

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
        where $k >= 0$, $C_0 -> D_0, ..., C_(k - 1) -> D_(k - 1)$ are arbitrary implications, and we set $Delta_I := {D_j : j in I}$ and $Gamma_I := {C_j : j in.not I}$.
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
The name $LogicSPL$ follows @Pet23.

#definition[
  We define _Solovay Propositional Logic_ $LogicSPL$ and  _Dzhaparidze Propositional Logic_ $LogicDPL$.
  - $LogicSPL := {A in FmlPL : GentzenDPL proves emptyset seq(2) {A}}$.
  - $LogicDPL := {A in FmlPL : GentzenDPL proves emptyset seq(3) {A}}$.
] <def:spl_dpl>

By comparing with @IKK01[Section 3], we see that the restriction of $GentzenDPL$ to level $1$ is almost the same as the sequent calculus for $LogicFPL$ introduced in @IKK01.
The only difference is that the initial sequents are restricted to propositional variables in $GentzenDPL$.
However, by @lem:gentzen_dpl_refl below, the derivable sequents do not change.
Therefore, $GentzenDPL proves emptyset seq(1) {A}$ if and only if $LogicFPL proves A$.

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

= Proof-theoretic embedding <sect:embedding>

The main result of this section is @thm:iff_visser: $GentzenDPL proves Gamma seq(level) Delta$ if and only if $GentzenD proves Gamma^Vis seq(level) Delta^Vis$.
We give a detailed proof based on the proofs in @YS17 @Pet23.

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
  We proceed by induction on $A$. The case $A equiv B or C$ is similar to the case $A equiv B and C$ and is omitted.

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
  Let $Gamma, Delta subset.eq FmlPL$ be finite and $level = 1, 2, 3$.
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
    Suppose that the last rule has the following form, where $Delta_I$ and $Gamma_I$ are as in @def:gentzen_dpl.
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
    We illustrate the case $k = 2$; this example is easy to generalize to arbitrary $k$.
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
    Then, applying $RImpL(1, 1)$ once more to the conclusions of $cal(D)_1$ and $cal(D)_2$, we obtain the desired sequent.
    $
      #prooftree(rule(
        name: $RImpL(1, 1)$,
        $Sigma^Vis, C_0^Vis -> D_0^Vis, C_1^Vis -> D_1^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$,
        subtree($cal(D)_1$, $Sigma^Vis, C_0^Vis -> D_0^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis, C_1^Vis$),
        subtree($cal(D)_2$, $D_1^Vis, Sigma^Vis, C_0^Vis -> D_0^Vis, Box (A^Vis -> B^Vis), A^Vis seq(1) B^Vis$),
      ))
    $
    Finally, we apply $RImpR(1, 1)$ and @lem:box_gl_visser with $Gamma := {C_j^Vis -> D_j^Vis : j < k}$.
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
    The conclusion is the desired sequent $Sigma^Vis, {C_j -> D_j : j < k}^Vis seq(1) (A -> B)^Vis$.
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
        ih($Gamma^Vis seq(2) Delta^Vis, A^Vis$, to: [left premise]),
        ih($B^Vis, Gamma^Vis seq(2) Delta^Vis$, to: [right premise]),
      ))),
    )
    The conclusion is the desired sequent $(A -> B)^Vis, Gamma^Vis seq(2) Delta^Vis$.
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
    which is the desired sequent ${A_i -> B_i : i < n}^Vis, Phi^Vis seq(3) {C_j -> D_j : j < m}^Vis$.
  ]

]

Next, we prove the converse of @lem:visser, following the strategy of @YS17[Lemma 7].
We proceed by induction on the height of a derivation in $GentzenD$ of a sequent built from $(dot)^Vis$ translation.
Here, unlike the usual definition, we modify the definition of height slightly as follows.

#definition[
  The _height_ $height(cal(D))$ of a derivation $cal(D)$ in $GentzenD$ is the maximum, over all branches of $cal(D)$, of the number of applications of rules _except_ $RWk(level, level)$ on that branch.
  We write $GentzenD provesh(h) Gamma seq(level) Delta$ if $Gamma seq(level) Delta$ has a derivation in $GentzenD$ of height at most $h$ in this sense.
] <def:height>


We explain why this modification is needed.
As mentioned in @rem:visser_unfolded, $p^Vis$, $(B and C)^Vis$ and $(B or C)^Vis$ are in fact implications, so the last rule of a derivation of such a sequent may be a rule for $->$ of $GentzenD$.
In this case, going back through the rule for $->$ of $GentzenD$, the premise must contain a formula that is not obtained by the translation $(dot)^Vis$, such as $B^Vis -> (C^Vis -> bot)$.
We remove such formulas by the inversion rules $Inv(RImpL(level, level))$ and $Inv(RImpR(level, level))$ (@lem:inv_imp_l and @lem:inv_imp_r), then apply the induction hypothesis, and finally apply suitable rules to return to the desired sequent.
When the cases are analysed in detail according to the form of the formulas, applying the induction hypothesis may erase some formulas, such as $bot$ and the antecedent or the consequent of $->$.
So, they have to be supplied again by $RWk(level, level)$, and unless this weakening is prevented from increasing the height, the resulting derivation would have a height greater than that of the desired conclusion.
Note that with this modified height, if the last rule of a derivation $cal(D)$ of $GentzenD$ is a weakening, the height of the derivation of its premise may be equal to $height(cal(D))$, so the usual induction on the height alone cannot be used.
Instead, we use induction along the lexicographic order on the pairs $(height(cal(D)), mrm("rules")(cal(D)))$, where $mrm("rules")(cal(D))$ is the number of applications of rules in $cal(D)$; since this order is well-founded, the induction is justified.

We first collect the syntactic properties of the translation $(dot)^Vis$ that this requires.

#lemma[
  + No element of $FmlPL^Vis$ is a propositional variable or of the form $Box p$ with $p in PropVar$.
  + An element of $FmlPL^Vis$ that is an implication is of the form $p^Vis$, $(B and C)^Vis$ or $(B or C)^Vis$, and one that is of the form $Box E$ is of the form $(B -> C)^Vis$.
  + $A^Vis equiv bot$ iff $A equiv bot$.
  + The antecedent of every implication in $FmlPL^Vis$ is an implication.
] <lem:visser_shape>

#proof[
  All claims follow from the following list, which gives the shape of $A^Vis$ for each form of $A$ (see @rem:visser_unfolded).
  - If $A equiv p$, then $p^Vis equiv (p -> (Box p -> bot)) -> bot$, an implication with the antecedent $p -> (Box p -> bot)$.
  - If $A equiv bot$, then $bot^Vis equiv bot$.
  - If $A equiv B and C$, then $(B and C)^Vis equiv (B^Vis -> (C^Vis -> bot)) -> bot$, an implication with the antecedent $B^Vis -> (C^Vis -> bot)$.
  - If $A equiv B or C$, then $(B or C)^Vis equiv (B^Vis -> bot) -> C^Vis$, an implication with the antecedent $B^Vis -> bot$.
  - If $A equiv B -> C$, then $(B -> C)^Vis equiv Box (B^Vis -> C^Vis)$.
  In particular, the antecedents $p -> (Box p -> bot)$, $B^Vis -> (C^Vis -> bot)$ and $B^Vis -> bot$ of the implications among translations are themselves implications.
]

#lemma[
  If $A in FmlPL^Vis$, then $A -> B in.not FmlPL^Vis$ for every $B in FmlML$.
] <lem:visser_not_imp>

#proof[
  We prove the claim by induction on $A$.
  Suppose, for a contradiction, that $A in FmlPL^Vis$ and $A -> B in FmlPL^Vis$.
  By @lem:visser_shape, the implication $A -> B$ is $p^Vis$, $(C and D)^Vis$ or $(C or D)^Vis$.
  - If $A -> B equiv p^Vis$, then $A equiv p -> (Box p -> bot)$, whose antecedent is not an implication; this contradicts @lem:visser_shape.
  - If $A -> B equiv (C and D)^Vis$, then $A equiv C^Vis -> (D^Vis -> bot)$, so $C^Vis$ is a proper subformula of $A$ with $C^Vis in FmlPL^Vis$ and $C^Vis -> (D^Vis -> bot) in FmlPL^Vis$, which contradicts the induction hypothesis.
  - If $A -> B equiv (C or D)^Vis$, then $A equiv C^Vis -> bot$, so $C^Vis$ is a proper subformula of $A$ with $C^Vis in FmlPL^Vis$ and $C^Vis -> bot in FmlPL^Vis$, which contradicts the induction hypothesis.
]

#lemma[
  If $GentzenD provesh(h) Gamma seq(level) Delta$, then $GentzenD provesh(h) Gamma seq(level) Delta without {bot}$.
] <lem:erase_bot>

#proof[
  By structural induction on a derivation $cal(D)$ of $Gamma seq(level) Delta$, for all $Gamma$, $Delta$ and $level$, we show that there is a derivation of $Gamma seq(level) Delta without {bot}$ whose height is at most $h := height(cal(D))$.
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
    - If $C equiv.not bot$:
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
          ih($GentzenD provesh(h-1) Gamma' seq(level) Delta without {bot}, C$, to: [left premise]),
          ih($GentzenD provesh(h-1) D, Gamma' seq(level) Delta without {bot}$, to: [right premise]),
        )),
      )
    - If $C equiv bot$:
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
    - If $D equiv.not bot$:
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
    - If $D equiv bot$:
      Note that if the application of $RWk(level, level)$ here increased the height, we could not obtain a derivation of height at most $h$.
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
  ]

]

#lemma[Inversion rules $Inv(RImpL(level, level))$ of $GentzenD$][
  Let $level = 1, 2, 3$ and $h >= 0$, and let $A -> B in.not Gamma$.
  Then the following rules are height-preserving admissible in $GentzenD$.
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
  We refer to the conclusion of the first rule as the _left conclusion_ and to that of the second as the _right conclusion_.
] <lem:inv_imp_l>

#proof[
  Fix $A$ and $B$.
  We prove both claims simultaneously, for all $Gamma$, $Delta$ and $level$ with $A -> B in.not Gamma$, by induction on a derivation $cal(D)$ of $A -> B, Gamma seq(level) Delta$, distinguishing cases by the last rule of $cal(D)$.
  Except in some cases, we display only the derivations for the left conclusion; the right conclusion is obtained in the same way.

  #struct[Case $RAx(level)$, $RBotL(level)$, $RBoxGL(1, 1)$, $RLift(2, 3)$][
    The antecedent of the conclusion consists only of propositional variables, $bot$ and formulas of the form $Box C$, so it does not contain $A -> B$.
    Thus this case does not occur.
  ]

  #struct[Case $RWk(level, level)$][
    The premise is $Gamma_0 seq(level) Delta_0$ with $Gamma_0 subset.eq {A -> B} union Gamma$ and $Delta_0 subset.eq Delta$, and it has height at most $h$.
    - If $A -> B in Gamma_0$, then $Gamma_0 = A -> B, Gamma_1$ for some $Gamma_1 subset.eq Gamma$ with $A -> B in.not Gamma_1$:
      #rewrite(
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) A -> B, Gamma seq(level) Delta$,
          $GentzenD provesh(h) A -> B, Gamma_1 seq(level) Delta_0$,
        )),
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta, A$,
          ih($GentzenD provesh(h) Gamma_1 seq(level) Delta_0, A$),
        )),
      )
    - If $A -> B in.not Gamma_0$, then $Gamma_0 subset.eq Gamma$:
      #rewrite(
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) A -> B, Gamma seq(level) Delta$,
          $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
        )),
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) Delta, A$,
          $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
        )),
      )
  ]

  #struct[Case $RImpL(level, level)$][
    Let $C -> D$ be the principal formula of the last rule, and $Gamma_1$ the rest of the antecedent, so that $C -> D, Gamma_1 = A -> B, Gamma$.
    #wide(prooftree(rule(
      name: $RImpL(level, level)$,
      $GentzenD provesh(h) C -> D, Gamma_1 seq(level) Delta$,
      $GentzenD provesh(h-1) Gamma_1 seq(level) Delta, C$,
      $GentzenD provesh(h-1) D, Gamma_1 seq(level) Delta$,
    )))
    - If $C -> D equiv A -> B$ and $A -> B in.not Gamma_1$, then $Gamma_1 = Gamma$, and the left and right premises are already the left and right conclusions, respectively.
    - If $C -> D equiv A -> B$ and $A -> B in Gamma_1$, then $Gamma_1 = A -> B, Gamma$.
      The left premise is $A -> B, Gamma seq(level) Delta, A$, to which we apply the induction hypothesis for the left conclusion, and the right premise is $A -> B, B, Gamma seq(level) Delta$, to which we apply the induction hypothesis for the right conclusion; note that $A -> B in.not B, Gamma$.
      $
        #ih($GentzenD provesh(h-1) Gamma seq(level) Delta, A$, to: [left conclusion]) quad quad #ih($GentzenD provesh(h-1) B, Gamma seq(level) Delta$, to: [right conclusion])
      $
    - If $C -> D equiv.not A -> B$, then $A -> B in Gamma_1$; write $Gamma_1 = A -> B, Gamma_2$ with $A -> B in.not Gamma_2$, so that $Gamma = C -> D, Gamma_2$.
      The premises are $A -> B, Gamma_2 seq(level) Delta, C$ and $D, A -> B, Gamma_2 seq(level) Delta$.
      - If $D equiv.not A -> B$:
        #wide(prooftree(rule(
          name: $RImpL(level, level)$,
          $GentzenD provesh(h) C -> D, Gamma_2 seq(level) Delta, A$,
          ih($GentzenD provesh(h-1) Gamma_2 seq(level) Delta, C, A$, to: [left premise]),
          ih($GentzenD provesh(h-1) D, Gamma_2 seq(level) Delta, A$, to: [right premise]),
        )))
      - If $D equiv A -> B$, the right premise is $A -> B, Gamma_2 seq(level) Delta$:
        #wide(prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h-1) C -> D, Gamma_2 seq(level) Delta, A$,
          ih($GentzenD provesh(h-1) Gamma_2 seq(level) Delta, A$),
        )))
  ]

  #struct[Case $RImpR(level, level)$][
    The last rule is of the form below, where $Delta = Delta' union {C -> D}$.
    $
      #prooftree(rule(
        name: $RImpR(level, level)$,
        $GentzenD provesh(h) A -> B, Gamma seq(level) Delta', C -> D$,
        $GentzenD provesh(h-1) C, A -> B, Gamma seq(level) Delta', D$,
      ))
    $
    - If $C equiv.not A -> B$, then $A -> B in.not C, Gamma$:
      #wide(prooftree(rule(
        name: $RImpR(level, level)$,
        $GentzenD provesh(h) Gamma seq(level) Delta', C -> D, A$,
        ih($GentzenD provesh(h-1) C, Gamma seq(level) Delta', D, A$),
      )))
    - If $C equiv A -> B$, the premise is $A -> B, Gamma seq(level) Delta', D$:
      #wide(prooftree(rule(
        name: $RImpR(level, level)$,
        $GentzenD provesh(h) Gamma seq(level) Delta', (A -> B) -> D, A$,
        rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h-1) A -> B, Gamma seq(level) Delta', D, A$,
          ih($GentzenD provesh(h-1) Gamma seq(level) Delta', D, A$),
        ),
      )))
  ]

  #struct[Case $RBoxL(2, 2)$][
    Here $A -> B, Gamma = Box C, Gamma_1$; since $Box C equiv.not A -> B$, we have $A -> B in Gamma_1$.
    Write $Gamma_1 = A -> B, Gamma_2$ with $A -> B in.not Gamma_2$, so that $Gamma = Box C, Gamma_2$.
    #wide(prooftree(rule(
      name: $RBoxL(2, 2)$,
      $GentzenD provesh(h) Box C, A -> B, Gamma_2 seq(2) Delta$,
      $GentzenD provesh(h-1) C, A -> B, Gamma_2 seq(2) Delta$,
    )))
    - If $C equiv.not A -> B$:
      #wide(prooftree(rule(
        name: $RBoxL(2, 2)$,
        $GentzenD provesh(h) Box C, Gamma_2 seq(2) Delta, A$,
        ih($GentzenD provesh(h-1) C, Gamma_2 seq(2) Delta, A$),
      )))
    - If $C equiv A -> B$, the premise is $A -> B, Gamma_2 seq(2) Delta$:
      #wide(prooftree(rule(
        name: $RWk(2, 2)$,
        $GentzenD provesh(h-1) Box C, Gamma_2 seq(2) Delta, A$,
        ih($GentzenD provesh(h-1) Gamma_2 seq(2) Delta, A$),
      )))
  ]

  #struct[Case $RLift(1, 2)$][
    #rewrite(
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) A -> B, Gamma seq(2) Delta$,
        $GentzenD provesh(h-1) A -> B, Gamma seq(1) Delta$,
      )),
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) Gamma seq(2) Delta, A$,
        ih($GentzenD provesh(h-1) Gamma seq(1) Delta, A$),
      )),
    )
  ]

]

#lemma[Inversion rule $Inv(RImpR(level, level))$ of $GentzenD$][
  Let $level = 1, 2, 3$ and $h >= 0$, and let $A -> B in.not Delta$.
  Then the following rule is height-preserving admissible in $GentzenD$.
  $
    #prooftree(rule(
      name: $Inv(RImpR(level, level))$,
      $GentzenD provesh(h) A, Gamma seq(level) Delta, B$,
      $GentzenD provesh(h) Gamma seq(level) Delta, A -> B$,
    ))
  $
] <lem:inv_imp_r>

#proof[
  Fix $A$ and $B$.
  We prove the claim for all $Gamma$, $Delta$ and $level$ with $A -> B in.not Delta$ by induction on a derivation $cal(D)$ of $Gamma seq(level) A -> B, Delta$, distinguishing cases by the last rule of $cal(D)$.

  #struct[Case $RAx(level)$, $RBotL(level)$, $RBoxGL(1, 1)$, $RLift(2, 3)$][
    The succedent of the conclusion consists only of propositional variables and formulas of the form $Box C$, so it does not contain $A -> B$.
    Thus this case does not occur.
  ]

  #struct[Case $RWk(level, level)$][
    The premise is $Gamma_0 seq(level) Delta_0$ with $Gamma_0 subset.eq Gamma$ and $Delta_0 subset.eq {A -> B} union Delta$, and it has height at most $h$.
    - If $A -> B in Delta_0$, then $Delta_0 = A -> B, Delta_1$ for some $Delta_1 subset.eq Delta$ with $A -> B in.not Delta_1$:
      #rewrite(
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) A -> B, Delta$,
          $GentzenD provesh(h) Gamma_0 seq(level) A -> B, Delta_1$,
        )),
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) A, Gamma seq(level) Delta, B$,
          ih($GentzenD provesh(h) A, Gamma_0 seq(level) Delta_1, B$),
        )),
      )
    - If $A -> B in.not Delta_0$, then $Delta_0 subset.eq Delta$:
      #rewrite(
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) Gamma seq(level) A -> B, Delta$,
          $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
        )),
        prooftree(rule(
          name: $RWk(level, level)$,
          $GentzenD provesh(h) A, Gamma seq(level) Delta, B$,
          $GentzenD provesh(h) Gamma_0 seq(level) Delta_0$,
        )),
      )
  ]

  #struct[Case $RImpL(level, level)$][
    Let $C -> D$ be the principal formula of the last rule, so that $Gamma = C -> D, Gamma_1$.
    #wide(prooftree(rule(
      name: $RImpL(level, level)$,
      $GentzenD provesh(h) C -> D, Gamma_1 seq(level) A -> B, Delta$,
      $GentzenD provesh(h-1) Gamma_1 seq(level) A -> B, Delta, C$,
      $GentzenD provesh(h-1) D, Gamma_1 seq(level) A -> B, Delta$,
    )))
    - If $C equiv.not A -> B$:
      #wide(prooftree(rule(
        name: $RImpL(level, level)$,
        $GentzenD provesh(h) A, C -> D, Gamma_1 seq(level) Delta, B$,
        ih($GentzenD provesh(h-1) A, Gamma_1 seq(level) Delta, C, B$, to: [left premise]),
        ih($GentzenD provesh(h-1) A, D, Gamma_1 seq(level) Delta, B$, to: [right premise]),
      )))
    - If $C equiv A -> B$, the left premise is $Gamma_1 seq(level) A -> B, Delta$:
      #wide(prooftree(rule(
        name: $RWk(level, level)$,
        $GentzenD provesh(h-1) A, C -> D, Gamma_1 seq(level) Delta, B$,
        ih($GentzenD provesh(h-1) A, Gamma_1 seq(level) Delta, B$, to: [left premise]),
      )))
  ]

  #struct[Case $RImpR(level, level)$][
    Let $C -> D$ be the principal formula of the last rule, and $Delta_1$ the rest of the succedent, so that $C -> D, Delta_1 = A -> B, Delta$.
    #wide(prooftree(rule(
      name: $RImpR(level, level)$,
      $GentzenD provesh(h) Gamma seq(level) C -> D, Delta_1$,
      $GentzenD provesh(h-1) C, Gamma seq(level) Delta_1, D$,
    )))
    - If $C -> D equiv A -> B$ and $A -> B in.not Delta_1$, then $Delta_1 = Delta$, and the premise is the desired sequent.
    - If $C -> D equiv A -> B$ and $A -> B in Delta_1$, then $Delta_1 = A -> B, Delta$.
      The premise is $A, Gamma seq(level) A -> B, Delta, B$; note that $B equiv.not A -> B$.
      $
        #ih($GentzenD provesh(h-1) A, Gamma seq(level) Delta, B$)
      $
    - If $C -> D equiv.not A -> B$, then $A -> B in Delta_1$; write $Delta_1 = A -> B, Delta_2$ with $A -> B in.not Delta_2$, so that $Delta = C -> D, Delta_2$.
      The premise is $C, Gamma seq(level) A -> B, Delta_2, D$.
      - If $D equiv.not A -> B$:
        #wide(prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) A, Gamma seq(level) Delta_2, C -> D, B$,
          ih($GentzenD provesh(h-1) A, C, Gamma seq(level) Delta_2, D, B$),
        )))
      - If $D equiv A -> B$, the premise is $C, Gamma seq(level) A -> B, Delta_2$:
        #wide(prooftree(rule(
          name: $RImpR(level, level)$,
          $GentzenD provesh(h) A, Gamma seq(level) Delta_2, C -> (A -> B), B$,
          rule(
            name: $RWk(level, level)$,
            $GentzenD provesh(h-1) A, C, Gamma seq(level) Delta_2, A -> B, B$,
            ih($GentzenD provesh(h-1) A, C, Gamma seq(level) Delta_2, B$),
          ),
        )))
  ]

  #struct[Case $RBoxL(2, 2)$][
    Here $Gamma = Box C, Gamma_1$.
    #rewrite(
      prooftree(rule(
        name: $RBoxL(2, 2)$,
        $GentzenD provesh(h) Box C, Gamma_1 seq(2) A -> B, Delta$,
        $GentzenD provesh(h-1) C, Gamma_1 seq(2) A -> B, Delta$,
      )),
      prooftree(rule(
        name: $RBoxL(2, 2)$,
        $GentzenD provesh(h) A, Box C, Gamma_1 seq(2) Delta, B$,
        ih($GentzenD provesh(h-1) A, C, Gamma_1 seq(2) Delta, B$),
      )),
    )
  ]

  #struct[Case $RLift(1, 2)$][
    #rewrite(
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) Gamma seq(2) A -> B, Delta$,
        $GentzenD provesh(h-1) Gamma seq(1) A -> B, Delta$,
      )),
      prooftree(rule(
        name: $RLift(1, 2)$,
        $GentzenD provesh(h) A, Gamma seq(2) Delta, B$,
        ih($GentzenD provesh(h-1) A, Gamma seq(1) Delta, B$),
      )),
    )
  ]
]

#lemma[cf. @Pet23[Lemma 5]][
  Let $Gamma, Delta subset.eq FmlPL$ and $Phi_1, Phi_2, Psi subset.eq PropVar$ be finite sets and $level = 1, 2, 3$.
  If $GentzenD proves Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis$,
  then $GentzenDPL proves Gamma, Phi_1, Phi_2 seq(level) Psi, Delta$.
] <lem:of_visser>

#proof[
  Let $cal(D)$ be a derivation of the $GentzenD proves Gamma^Vis, Phi_1, Box Phi_2 seq(level) Psi, Delta^Vis$ and $h := height(cal(D))$.
  The induction hypothesis is taken for all $Gamma$, $Delta$, $Phi_1$, $Phi_2$, $Psi$ and $level$:
  in each case below, we write a sequent obtained from the premises of the last rule in the form $Gamma'^Vis, Phi'_1, Box Phi'_2 seq(level) Psi', Delta'^Vis$, with components different from those of the conclusion, and apply the induction hypothesis to it.
  In each case we display the last rule, the derivations in $GentzenD$ obtained from its premises by $Inv(RImpL(level, level))$ and $Inv(RImpR(level, level))$, and the derivation in $GentzenDPL$ built from the sequents given by the induction hypothesis.

  We first note the following.
  By @lem:visser_shape, the three sets $Gamma^Vis$, $Phi_1$ and $Box Phi_2$ are pairwise disjoint, as are $Psi$ and $Delta^Vis$;
  an element of $Gamma^Vis$ or $Delta^Vis$ that is an implication is $p^Vis$, $(A and B)^Vis$ or $(A or B)^Vis$, and one that is boxed is $(A -> B)^Vis$.
  Since $GentzenDPL$ has $RWk(level, level)$, it suffices to derive in $GentzenDPL$ a sequent whose antecedent is a subset of $Gamma, Phi_1, Phi_2$ and whose succedent is a subset of $Psi, Delta$.
  Since $RWk(level, level)$ of $GentzenD$ does not increase the height, a sequent of height at most $h - 1$ may be weakened before the induction hypothesis is applied to it.

  #struct[Case $RAx(level)$][
    The sequent is $p seq(level) p$.
    By @lem:visser_shape, $p in Phi_1$ and $p in Psi$, and $RAx(level)$ of $GentzenDPL$ gives $p seq(level) p$.
  ]

  #struct[Case $RBotL(level)$][
    The sequent is $bot seq(level)$.
    By @lem:visser_shape, $bot in Gamma$, and $RBotL(level)$ of $GentzenDPL$ gives $bot seq(level)$.
  ]

  #struct[Case $RWk(level, level)$][
    The induction hypothesis applies to the subderivation of the premise, whose height is at most $h$ and which has fewer applications of rules than $cal(D)$.
    The antecedent of the premise is a subset of $Gamma^Vis, Phi_1, Box Phi_2$, hence of the form $Gamma'^Vis, Phi'_1, Box Phi'_2$ with $Gamma' subset.eq Gamma$, $Phi'_1 subset.eq Phi_1$ and $Phi'_2 subset.eq Phi_2$;
    similarly its succedent is of the form $Psi', Delta'^Vis$ with $Psi' subset.eq Psi$ and $Delta' subset.eq Delta$.
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
    The principal formula is an implication in the antecedent, so it is $A^Vis$ for some $A in Gamma$ with $A equiv p, B and C, B or C$.
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
      The formula $B^Vis -> (C^Vis -> bot)$ is not in $FmlPL^Vis$ by @lem:visser_not_imp, since $B^Vis in FmlPL^Vis$.
      Also $C^Vis -> bot$ is not in $FmlPL^Vis$ by the same lemma, since $C^Vis in FmlPL^Vis$.
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
      The formula $B^Vis -> bot$ is not in $FmlPL^Vis$ by @lem:visser_not_imp, since $B^Vis in FmlPL^Vis$.
      Hence it does not belong to $Psi, Delta^Vis$, and applying $Inv(RImpR(level, level))$ to the left premise we obtain the following.
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
    The principal formula is an implication in the succedent, so it is $A^Vis$ for some $A in Delta$ with $A equiv p, B and C, B or C$.
    By @lem:visser_shape, there is $Delta' subset.eq Delta$ with $Delta = Delta' union {A}$ such that the rest of the succedent is $Psi, Delta'^Vis$ (possibly $A in Delta'$).
    The formulas inverted below are among those treated in the case $RImpL(level, level)$, so they do not belong to $Gamma^Vis, Phi_1, Box Phi_2$.
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
      - If $B equiv bot$, then $B^Vis equiv bot$, so @lem:erase_bot removes $B^Vis$, and we add it back by $RWk(level, level)$:
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
      - If $C equiv bot$, then $C^Vis equiv bot$, so @lem:erase_bot removes $C^Vis$, and we add it back by $RWk(level, level)$:
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
    These applications of $Inv(RImpR(1, 1))$ and $Inv(RImpL(1, 1))$ are legitimate, since each inverted formula differs from the other formulas on its side:
    - $A^Vis$ and the $D_j^Vis$ belong to $FmlPL^Vis$, whereas the $C_j^Vis -> D_j^Vis$ do not, by @lem:visser_not_imp;
    - $Phi_2$ consists of propositional variables, and $Gamma^Vis$, $Box Phi_2$ and $(A -> B)^Vis$ consist of boxed formulas;
    - $C_i^Vis -> D_i^Vis equiv.not C_j^Vis -> D_j^Vis$ for $i eq.not j$, by the injectivity of $(dot)^Vis$.

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
    - If the principal formula is $Box q$ for some $q in Phi_2$: let $Phi'_2 subset.eq Phi_2$ be such that $Phi'_2 union {q} = Phi_2$ and the rest of the antecedent is $Gamma^Vis, Phi_1, Box Phi'_2$ (possibly $q in Phi'_2$).
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
    - If the principal formula is $(A -> B)^Vis$ for some $A -> B in Gamma$: let $Gamma'$ be as in the case $RImpL(level, level)$, so that $Gamma' union {A -> B} = Gamma$ and the last rule is the following:
      #wide(prooftree(rule(
        name: $RBoxL(2, 2)$,
        $GentzenD provesh(h) (A -> B)^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
        $GentzenD provesh(h-1) A^Vis -> B^Vis, Gamma'^Vis, Phi_1, Box Phi_2 seq(2) Psi, Delta^Vis$,
      )))
      $A^Vis -> B^Vis$ does not belong to $FmlPL^Vis$ by @lem:visser_not_imp, and hence not to $Gamma'^Vis, Phi_1, Box Phi_2$, so the left and right conclusions of $Inv(RImpL(2, 2))$, applied to the premise, give the following.
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
  // The first equivalences of items 2 and 3 are the definitions of $LogicSPL$ and $LogicDPL$, and that of item 1 is the remark after @def:spl_dpl.
]
*/

#remark[
  In particular, item 1 of @cor:mem_logic_iff gives a proof-theoretic proof of the equivalence of items 1 and 2 of @prop:visser_fpl; this case is not treated in @YS17.
] <rem:visser_fpl_embedding>

Combining @thm:iff_visser with @prop:gentzen_d_cut, we obtain the cut-admissibility of $GentzenDPL$.

#corollary[Cut-admissibility of $GentzenDPL$][
  The rule $RCut(level, level)$ is admissible in $GentzenDPL$.
] <cor:gentzen_dpl_cut>

== Errors in Petrukhin's proof <sect:errors_in_petrukhin>

Our embedding result builds on Petrukhin @Pet23, whose proof, however, contains errors.
All of them concern @Pet23[Lemma 5], which corresponds to @lem:of_visser of the present paper; we point them out below.
We state it in terms of the calculi used in @Pet23, namely Kushida's sequent calculus for $LogicS$ @Kus20 and Petrukhin's sequent calculus for $LogicSPL$; their sequents are based on _multisets_, and the names of the rules are adapted to ours except where noted.

#proposition(numbering: none)[@Pet23[Lemma 5]][
  If Kushida's sequent calculus for $LogicS$ proves $Gamma^Vis, Phi, Box Phi seq(level) Psi, Delta^Vis$, then Petrukhin's sequent calculus for $LogicSPL$ proves $Gamma, Phi seq(level) Psi, Delta$.
  Here $Gamma, Delta$ are multisets of formulas and $Phi, Psi$ are multisets of propositional variables.
]

Petrukhin's proof proceeds by induction on the height #footnote[Petrukhin does not define the height; we understand it as the usual one, which counts every application of a rule, unlike our height in @def:height.] of a derivation of $Gamma^Vis, Phi, Box Phi seq(level) Psi, Delta^Vis$ in Kushida's calculus.
He states that a significant part of the cases coincide with those in the proof of @YS17[Lemma 7] or can be obtained from them by slight modifications, but a problem arises in the case $RBoxL(2, 2)$, which is written $(Box arrow.r.double)$ in @Pet23, and similarly in the case of the other rule $(Box arrow.r)$ for $Box$ in the antecedent.
Petrukhin verifies only the case where the principal formula is $Box(E^Vis -> F^Vis)$.
Moreover, the treatment of this case is itself incorrect.
The derivation given there is the following (see @Pet23[p.~17]; here $provesh(h)$ refers to this usual height).
$
  #prooftree(rule(
    name: $RBoxL(2, 2)$,
    $provesh(h) Box(E^Vis -> F^Vis), Gamma^Vis, Phi seq(2) Psi, Delta^Vis$,
    $provesh(h-1) E^Vis -> F^Vis, Gamma^Vis, Phi seq(2) Psi, Delta^Vis$,
  ))
$
There are two problems.
First, $Box Phi$ is missing from both the conclusion and the premise.
Second, even if we supply it and regard the premise as $provesh(h-1) E^Vis -> F^Vis, Gamma^Vis, Phi, Box Phi seq(2) Psi, Delta^Vis$, the induction hypothesis cannot be applied to this premise.
This is because $E^Vis -> F^Vis$ is neither a propositional variable nor an element of $FmlPL^Vis$ (@lem:visser_not_imp), so the premise is not of the form $Gamma^Vis, Phi, Box Phi seq(level) Psi, Delta^Vis$.
Nevertheless, Petrukhin applies the induction hypothesis to this premise and obtains $E -> F, Gamma, Phi seq(2) Psi, Delta$, which is not justified.

Moreover, Petrukhin's proof lacks the case where the principal formula is $Box p$ for some $p in Phi$.
In this case, the last rule is as follows.
$
  #prooftree(rule(
    name: $RBoxL(2, 2)$,
    $provesh(h) Box p, Gamma^Vis, p, Phi without {p}, Box(Phi without {p}) seq(2) Psi, Delta^Vis$,
    $provesh(h-1) p, Gamma^Vis, p, (Phi without {p}), Box(Phi without {p}) seq(2) Psi, Delta^Vis$,
  ))
$
Now, in order to apply the induction hypothesis to this premise and carry the argument through, one would need to add $Box p$ to the premise by _height-preserving_ weakening, obtaining, up to the multiplicity of $p$, $provesh(h-1) p, Box p, Gamma^Vis, (Phi without {p}), Box(Phi without {p}) seq(2) Psi, Delta^Vis$.
However, weakening is not height-preserving admissible in Kushida's calculus#footnote[For example, $p seq(2) p$ is an initial sequent, whereas $q, p seq(2) p$ is not, since the only initial sequents with a context are those for $bot$.].
This problem does not arise in @YS17, because their calculus for $LogicKFour$ has no rule that removes $Box$ from a formula in the antecedent: the premise of $(Box_4)$ contains both $Box Gamma$ and $Gamma$, so the form $Phi, Box Phi$ is preserved automatically#footnote[Their calculus is also G3-style (cf. @TS00): weakening and contraction are height-preserving admissible, and all rules except $(Box_4)$ are height-preserving invertible @YS17[p.~248]. However, @YS17 does not explain how these properties are proved for their calculus for $LogicKFour$.].

In this paper, these problems are avoided in @lem:of_visser as follows.
Since our sequents are based on _sets_, contraction is built into the formulation and never needs to be applied explicitly, let alone height-preservingly.
The case where the principal formula of $RBoxL(2, 2)$ is $Box(E^Vis -> F^Vis)$ is handled by the height-preserving inversion $Inv(RImpL(2, 2))$, which returns the premise to the form required by the induction hypothesis; the same device handles the cases of $RImpL(level, level)$ and $RImpR(level, level)$ whose principal formulas are $p^Vis$, $(A and B)^Vis$ or $(A or B)^Vis$ (@rem:visser_unfolded).
Moreover, the problematic case where the principal formula of $RBoxL(2, 2)$ is $Box p$ is absorbed by allowing the two sets of variables $Phi_1$ and $Phi_2$ in the statement to differ:
unboxing $Box p$ merely adds $p$ to $Phi_1$, so the induction hypothesis applies directly, without any height-preserving weakening or contraction in $GentzenD$.

= Semantics <sect:semantics>

// TODO:

= Concluding remarks and open problems <sect:conclusion>

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
the Visser--Gödel translation maps $p$ to $p and Box p$ precisely so that $Box p$ restores the persistence#footnote[For a Kripke model $chevron.l W, R, forces chevron.r$, if $x forces p$ and $x R y$ then $y forces p$.]
of Kripke models.
On the other hand, we believe that it should also be possible to define semantics for $LogicSPL$ directly
and to prove its completeness without going through the embedding, but so far we have not succeeded.
As for $LogicD$, semantics has been defined by Beklemishev @Bek89 @Bek90 and by Kashima et al.~@KKIM25.
Note that a discussion of the semantics of $LogicDPL$ via the embedding would be possible, but we did not present it here.

We consider the problem of semantics to be rather important, for the following somewhat subtle reason.
Suppose that there is a propositional logic that corresponds (or _should_ correspond) to $LogicS$ or $LogicD$.
Then, for practical purposes, we consider that the justification of the correspondence should be witnessed by
some semantics, such as Kripke-style or arithmetical interpretations.
In this paper, we defined the logics $LogicSPL$ and $LogicDPL$ by the sequent calculus $GentzenDPL$,
and we cannot eliminate the possibility that they are, in a sense, ad hoc logics built solely in order to claim the embeddability.
In other words, it is conceivable that different logics $LogicSPL'$ and $LogicDPL'$,
obtained by slightly modifying the definitions of $GentzenDPL$, can also be embedded into $LogicS$ and $LogicD$;
in such a case, one may ask what the difference between them really is, or object that they are _merely_ syntactically different.
If, on the other hand, the correspondence is matched precisely at the semantic level,
one could respond to such criticism with some substantial grounds.
For these reasons, we regard the semantic witnessing of $LogicSPL$ and $LogicDPL$ as a major problem for future work.

== Hilbert-style formulations

Hilbert-style systems for $LogicBPL$ and $LogicFPL$ have been studied in @SO97 @IKK01.
A natural question is then what Hilbert-style systems for $LogicSPL$ and $LogicDPL$ look like.
However, we defined $LogicSPL$ and $LogicDPL$ by a sequent calculus, and moreover by a sequent calculus with several levels of sequents.
Defining Hilbert-style systems seems to be far from easy.
In fact, we conjecture that no Hilbert-style system exists in the language with a single level of implication $->$.
If this conjecture is true, further questions arise:
what is a logic in a language equipped with several levels of implications $attach(->, tr: 1)$ and $attach(->, tr: 2)$,
and what do such implications mean?

== Syntactic cut-elimination

The embeddability and the cut-admissibility of our sequent calculus $GentzenDPL$ rely
on the cut-elimination for the sequent calculus for $LogicD$ of @KKIM25 (@prop:gentzen_d_cut); apart from this, the arguments in @sect:embedding are explicit transformations of derivations.
In @KKIM25 the cut-elimination is obtained by a reduction to the syntactic cut-elimination for Kushida's calculus @Kus20, and also by a semantic argument.
It is still open to give a direct, constructive cut-elimination procedure for the sequent calculus $GentzenDPL$ itself.
