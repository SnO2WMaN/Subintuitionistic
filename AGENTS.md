# Working in propositional-provability-logics

The contract for AI agents in this repository.

The project formalizes and verifies, in Lean 4, the research around [Nog26], and develops new
results on top of it. The Lean library is `Subintuitionistic`. Before formalizing a result, read
the Japanese proof notes in `.local/proofs/`.

## Setup

Skills (`imozuru`, `japanese-tech-writing`, `lean4`) are pinned in `skills-lock.json`. Restore
them with `npx skills experimental_install`, which writes `.agents/skills/`; Claude Code reads
them through the symlinks `.claude/skills/<name> -> ../../.agents/skills/<name>`. Both
directories are git-ignored.

## Local files

Everything personal, or anything that must not be version-controlled, goes under `.local/` at
the project root (git-ignored). Never commit it, and never put such files anywhere else.

| What | Where |
|---|---|
| Reference texts (PDFs of papers, books, …) | `.local/references/` |
| Personal mathematical notes | `.local/proofs/` |

The reference texts are copyrighted: cite them, never commit or quote them at length.

## Mathematical notes

Notes in `.local/proofs/` are Typst documents in Japanese, following the
`japanese-tech-writing` skill. Write them as mathematical documents: read
`.local/proofs/README.md` before writing a note, and start from `.local/proofs/template.typ`.
The template reads the bibliography from `references.yml` at the project root; compile from
`.local/proofs/` with `typst compile --root ../.. <note>.typ`.

## Lean

Follow the [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html);
the rules below add what is specific here and win where the two differ.

### Dependencies

Mathlib only. No other Lean library is imported, however much it overlaps; definitions are
written from scratch here. Search Mathlib before defining anything; only logical notions
(formulas, sequents, calculi, Kripke models, …) are defined from scratch.

### Checks

```bash
lake build Subintuitionistic --wfail   # no errors, no warnings
```

Never write `sorry` or `axiom`. Main theorems use only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Fix warnings; never suppress them. Never raise
`maxHeartbeats`. Every other `set_option` gets a one-line comment saying why.
`Subintuitionistic.lean` imports every module of the library.

### Files

Every file starts with `module`, uses `public import`, and puts its module docstring before
`@[expose] public section`. One topic, one file; do not over-split. Facts about propositional
logic go to `Subintuitionistic/Propositional/` (namespace `Propositional`), facts about modal
logic to `Subintuitionistic/Modal/` (namespace `Modal`), and results relating the two to
`Subintuitionistic/Translation/`. Lemmas mentioning nothing specific to this project go to
`Subintuitionistic/ToMathlib/`, at the path they would have in Mathlib. No compatibility layer:
a rename, move or deletion updates every use in the same change, with no aliases, wrappers or
shims.

### Notation and design

- Formulas: `#a`, `⊥`, `🡒`, `⋏`, `⋎` (and `□`, `∼`, `⊤` for modal formulas), scoped to the
  namespace `Propositional` or `Modal`. `FormulaSet α` and `FormulaFinset α` abbreviate sets
  and finite sets of formulas.
- Sequents are a structure per formula type, `Propositional.Sequent α` and `Modal.Sequent α`,
  with fields `ant` and `suc` and notation `Γ ⟹ Δ`. Layered sequents `Γ ⟹[ℓ] Δ`
  (`LayeredSequent α`, levels `ℓ : Fin 3`) are defined in the same `Sequent.lean`.
- Kripke models are structures with fields `Rel'` and `Val'` (and `hereditary'` for
  propositional models). Points are written `x : M.World` through `abbrev World`, so that the
  type keeps the model; never write `x : κ` for a point. `abbrev Rel` gives `x ≺ y`,
  `abbrev NotRel` gives `x ⊀ y`, and `abbrev Val` is the coercion `M x a`.
- Forcing is `x ⊩ A`, `x ⊩[M] A`, `x ⊮ A`, also for a sequent `x ⊩ S`; validity of a sequent in
  a model is `M ⊧ S`. Frame conditions are classes on models (`Model.IsFPL`,
  `Model.IsFiniteGL`).
- A sequent calculus is a `Type`-valued inductive `Derivation` of derivations, with notation
  `⊢ᴳ[𝐆𝐋]! S`, and derivability is `Derivable S := Nonempty (Derivation S)`, with notation
  `⊢ᴳ[𝐆𝐋] S` (and `⊬ᴳ[…] S`); likewise for `𝐅𝐏𝐋`, `𝐃`, `𝐃𝐏𝐋`. A calculus lives in the
  namespace of its logic (`Modal.logicGL.Derivation`, `Propositional.logicDPL.Derivable`, …).
  The rules are also stated as lemmas on `Derivable`, and `Derivable.rec` (an
  `@[induction_eliminator]`) is induction on derivability, so `induction h` works on `h : ⊢ᴳ[𝐆𝐋] S`.
  Heights of derivations are a recursive `Derivation.height`; do not index derivability by
  heights. Completeness is stated as
  `⊢ᴳ[𝐆𝐋] S ↔ ∀ {κ : Type u} (M : Model κ α), [M.IsFiniteGL] → M ⊧ S`.
- Translations are postfix: `Aᵍ` (Gödel), `Aᵛ` (Visser), and `Γᵍ`, `Γᵛ` on finite sets.
- Notation follows the code base, not the proof notes.
- Outside the structure instance that defines a model, use `M.Rel`, never the field `M.Rel'`:
  `M.Rel'` takes points of type `κ` and loses the model.
- The notations of the two sides overlap. Where both namespaces are open and an unannotated
  `x ≺ y` or `x ⊩ A` is ambiguous, use `x ⊩[M] A`, `M.Rel x y`, or `open … in`; do not add type
  ascriptions.

### Naming

Follow Mathlib's naming conventions, plus these word choices:

| Write | Not |
|---|---|
| upward closed | upset |
| unprovable | underivable |

- **General formulas** are Latin capitals `A`, `B`, `C`, …. Greek letters are reserved for
  formulas built by a specific construction and their parts.
- **Primes and subscripts** only distinguish several objects of the same type (`Γ Γ'`, or
  `Γ₁ Γ₂`). A lone object is `Γ`, not `Γ'`.
- **Intermediate `have`s** get short names (`h₁`, `h₂`, `hp`, `ih`); the type carries the
  meaning. Give a descriptive name only to a fact used several times.
- **Derivations** (terms of `Derivation S`) are `D`, `D₁`, `D₂`, `D'`.
- **A hypothesis `x ≺ y`** is named `Rxy` after its points (`Ryz`, `Rwv`, …); `x ⊀ y` is `nRxy`.
- **Constructions on models** are named after what they do, not after the letters of a source
  (`removeTerminals`, not `phi`).
- **Names after two or more people** start with the lowercase initials of their surnames. A name
  after one person keeps the surname (`gödel`, `visser`).
- **No named sets for an axiom schema.** Write the set-builder directly. Named logics are fine:
  a logic is `logicSPL : Logic α` (`Logic α` abbreviates `Set (Formula α)`), with notation
  `𝐒𝐏𝐋`. The logics are `𝐆𝐋`, `𝐒`, `𝐃` (namespace `Modal`) and `𝐅𝐏𝐋`, `𝐒𝐏𝐋`, `𝐃𝐏𝐋` (namespace
  `Propositional`). The namespace of a calculus is the `logicX` of its logic, not `X`.
- Declare universes (`universe u`) and bind every free variable explicitly; `autoImplicit` is
  off. Put implicit variables in `variable` inside a `section` or namespace, not ad hoc in
  statements. Write no redundant type ascriptions.

### Declarations

Extract lemmas that are reused; keep one-off lemmas inside their proof (no `_aux` lemmas: to
induct on a derivation of a non-variable sequent, `generalize` the sequent inside the proof); do not add what follows
from existing results in about two steps. Bundle lemmas into a `structure … : Prop` only when
three or more travel together through an induction. Attach `@[grind]` attributes (`=`, `.`,
`→`, `←`, …) actively to basic lemmas (forcing clauses, membership and inclusion facts, rules of a
calculus), and use `grind` in proofs wherever it shortens them. Use field notation (`t.f`) and
shorthand. Prefer constructive proofs.

### Proofs

Priorities: simple structure, then readability, then brevity. Tactic blocks follow Mathlib's
layout (one tactic per line, `·` for focus; a trailing `;` is allowed but not required). Split
any block over about thirty lines into lemmas.

| Avoid | Write |
|---|---|
| `refine ⟨n, ?_, ?_⟩` then `exact`s | `exact ⟨n, hn, hn.le⟩` |
| `refine ⟨f x, hf x, ?_⟩` | `use f x`, `and_intros`, one `·` per goal |
| `refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨_, _⟩ => …⟩` | `constructor` / `intro` / `rintro`, close each branch with `exact` |
| `refine f ?_` | `apply f` |
| `fun h => …` or `intro h` for `¬`, `∉`, `≠`, `⊮`, `⊀` | `by_contra h` (after `change ¬ …` if needed) |
| `exact s₁.trans <\| s₂.trans s₃` | `have`s, then `grind` / `simp_all` / `tauto` |
| `rw`, non-terminal `simp`, `simp only`, `simp at` | `have`, `suffices`, `change` |
| `f $ x`, `f (g x)` at the end of a term | `f <\| x` |
| `by exact t` | `t` |
| `show` restating the displayed goal | nothing |
| `have h := ih …` then `clear ih` | `replace ih := ih …` |
| `suffices ∀ S, …` then `clear` to induct on a non-variable sequent | `generalize hS : (Γ ⟹[ℓ] Δ) = S at D`, `induction D generalizing …`, `cases hS` |

Use `obtain` for existential witnesses. Prefer term-mode pattern matching for structural
induction.

### Comments and docstrings

English. A docstring says what the declaration states, never why or how it is proved; this holds
for module docstrings too. Comments only for what code cannot say, about one line. No
development artifacts: plan steps, issue numbers, `§2`-style labels, TODOs, stale skeleton
comments.

No docstring text that the declaration already says plainly (its name, signature or notation):
when only a citation is left, the docstring is the citation line alone; without a citation it is
omitted. Use the names and notations of the code base, not those of the papers (no `G_D`,
`G_DPL`; write `⊢ᴳ[𝐃]`, `logicDPL.Derivable`).

### Citations

Keys come from `references.yml` (Hayagriva, hand-edited); add a missing entry in the same
change. Every non-trivial `def`, `inductive`, `structure`, `abbrev` and `theorem` ends its
docstring with one line per key:

```
- [Vis81, Theorem 5.4]
- [IKK01, Lemma 2.6]
```

Never cite in running text. Supporting lemmas need no citation. Without per-declaration
docstrings, use a `## References` section in the module docstring. Without a source, omit the
docstring unless a short statement-level explanation helps.

### Refactoring

Keep the mathematics, simplify the structure, and report the line count before and after with
the percentage reduction.
