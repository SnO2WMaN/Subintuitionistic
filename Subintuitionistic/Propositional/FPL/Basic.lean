module

public import Subintuitionistic.Propositional.Sequent
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Prod

/-!
# The sequent calculus of `FPL`

`⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ` states that the sequent `Γ ⟹ Δ` is derivable. Besides the initial sequents
`A ⟹ A` and `⊥ ⟹`, weakening and the rules for `⋏` and `⋎`, the calculus has a single rule for
`🡒`: from the `2ⁿ` premises

  `Dᵢ (i ∈ I), Θ, A 🡒 B, A ⟹ B, Cᵢ (i ∉ I)`  for `I ⊆ {1, …, n}`

infer `Θ, C₁ 🡒 D₁, …, Cₙ 🡒 Dₙ ⟹ A 🡒 B`. The antecedent `A 🡒 B` of the premises is Löb's rule.
Here the implications `Cᵢ 🡒 Dᵢ` are given by a finite set `P` of pairs `(Cᵢ, Dᵢ)`, and `I` ranges
over the subsets of `P`.
-/

@[expose] public section

namespace Propositional

namespace FPL

variable {α : Type*} [DecidableEq α]

/-- The implications `C 🡒 D` for `(C, D) ∈ P`. -/
def imps (P : Finset (Formula α × Formula α)) : FormulaFinset α := P.image fun p ↦ p.1 🡒 p.2

/-- The sequent calculus of `FPL`.
- [IKK01, Section 3] -/
inductive Gentzen : Sequent α → Prop
  | axm (A) : Gentzen ({A} ⟹ {A})
  | botL : Gentzen ({⊥} ⟹ ∅)
  | wkL {Γ Γ' Δ} : Gentzen (Γ ⟹ Δ) → Γ ⊆ Γ' → Gentzen (Γ' ⟹ Δ)
  | wkR {Γ Δ Δ'} : Gentzen (Γ ⟹ Δ) → Δ ⊆ Δ' → Gentzen (Γ ⟹ Δ')
  | andL {Γ Δ A B} : Gentzen (insert A (insert B Γ) ⟹ Δ) → Gentzen (insert (A ⋏ B) Γ ⟹ Δ)
  | andR {Γ Δ A B} :
    Gentzen (Γ ⟹ insert A Δ) → Gentzen (Γ ⟹ insert B Δ) → Gentzen (Γ ⟹ insert (A ⋏ B) Δ)
  | orL {Γ Δ A B} :
    Gentzen (insert A Γ ⟹ Δ) → Gentzen (insert B Γ ⟹ Δ) → Gentzen (insert (A ⋎ B) Γ ⟹ Δ)
  | orR {Γ Δ A B} : Gentzen (Γ ⟹ insert A (insert B Δ)) → Gentzen (Γ ⟹ insert (A ⋎ B) Δ)
  | impR {Θ P A B} :
    (∀ I ⊆ P, Gentzen (insert (A 🡒 B) (insert A (Θ ∪ I.image Prod.snd)) ⟹
      insert B ((P \ I).image Prod.fst))) →
    Gentzen (Θ ∪ imps P ⟹ {A 🡒 B})

end FPL

@[inherit_doc] scoped[Propositional] notation:45 "⊢ᴳ[𝐅𝐏𝐋] " S:50 => FPL.Gentzen S
scoped[Propositional] notation:45 "⊬ᴳ[𝐅𝐏𝐋] " S:50 => ¬FPL.Gentzen S

namespace FPL.Gentzen

variable {α : Type*} [DecidableEq α] {Γ Γ' Δ Δ' : FormulaFinset α} {A : Formula α}

@[grind →] lemma wk (h : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐅𝐏𝐋] Γ' ⟹ Δ' :=
  wkR (wkL h hΓ) hΔ

@[grind →] lemma union (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ := (axm A).wk (by simpa) (by simpa)

@[grind ←] lemma botL_mem (h : ⊥ ∈ Γ) : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ := botL.wk (by simpa) (Finset.empty_subset _)

end FPL.Gentzen

end Propositional

end
