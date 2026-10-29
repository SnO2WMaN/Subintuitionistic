module

public import Subintuitionistic.Propositional.Formula
public import Subintuitionistic.ToMathlib.Order.Preorder.Finite

/-!
# Sequents of propositional formulas

A sequent `Γ ⟹ Δ` is a pair of finite sets of formulas. `S ⊆ T` is inclusion side by side, so
`S ⊆ (Λ ⟹ Λ)` states that every formula of `S` is in `Λ`. A layered sequent `Γ ⟹[ℓ] Δ` is a
sequent with a level `ℓ : Fin 3`; the levels `0`, `1`, `2` belong to `FPL`, `SPL` and `DPL`.
-/

@[expose] public section

namespace Propositional

structure Sequent (α : Type*) where
  ant : FormulaFinset α
  suc : FormulaFinset α

scoped[Propositional] infix:50 " ⟹ " => Sequent.mk

namespace Sequent

variable {α : Type*} {S T : Sequent α} {Λ : FormulaFinset α}

@[ext] lemma ext (ha : S.ant = T.ant) (hs : S.suc = T.suc) : S = T := by
  cases S; cases T; simp_all

instance : HasSubset (Sequent α) := ⟨fun S T ↦ S.ant ⊆ T.ant ∧ S.suc ⊆ T.suc⟩

@[grind =] lemma subset_iff : S ⊆ T ↔ S.ant ⊆ T.ant ∧ S.suc ⊆ T.suc := Iff.rfl

lemma exists_maximal (P : Sequent α → Prop) (hS : S ⊆ (Λ ⟹ Λ)) (h : ¬P S) :
    ∃ T, S ⊆ T ∧ T ⊆ (Λ ⟹ Λ) ∧ ¬P T ∧ ∀ U, T ⊆ U → U ⊆ (Λ ⟹ Λ) → ¬P U → U = T := by
  obtain ⟨Γ, Δ, h₁, h₂, h₃, h₄, h₅, hmax⟩ :=
    Finset.exists_maximal_pair (P := fun Γ Δ ↦ P (Γ ⟹ Δ)) hS.1 hS.2 h
  exact ⟨Γ ⟹ Δ, ⟨h₁, h₃⟩, ⟨h₂, h₄⟩, h₅, fun U hU₁ hU₂ hU ↦
    (hmax U.ant U.suc hU₁.1 hU₂.1 hU₁.2 hU₂.2 hU).elim ext⟩

/-- - [IKK01, Definition 2.5] -/
structure Saturated (S : Sequent α) : Prop where
  andL : ∀ {A B}, A ⋏ B ∈ S.ant → A ∈ S.ant ∧ B ∈ S.ant
  andR : ∀ {A B}, A ⋏ B ∈ S.suc → A ∈ S.suc ∨ B ∈ S.suc
  orL  : ∀ {A B}, A ⋎ B ∈ S.ant → A ∈ S.ant ∨ B ∈ S.ant
  orR  : ∀ {A B}, A ⋎ B ∈ S.suc → A ∈ S.suc ∧ B ∈ S.suc

variable [DecidableEq α]

def subfmls (S : Sequent α) : FormulaFinset α := (S.ant ∪ S.suc).subfmls

@[grind .] lemma subset_subfmls : S ⊆ (S.subfmls ⟹ S.subfmls) :=
  ⟨Finset.subset_union_left.trans FormulaFinset.subset_subfmls,
    Finset.subset_union_right.trans FormulaFinset.subset_subfmls⟩

lemma subformulaClosed_subfmls : S.subfmls.SubformulaClosed :=
  FormulaFinset.subformulaClosed_subfmls

end Sequent

/-- - [Nog26] -/
structure LayeredSequent (α : Type*) extends Sequent α where
  level : Fin 3

scoped[Propositional] notation:50 Γ:51 " ⟹[" ℓ "] " Δ:51 => LayeredSequent.mk (Sequent.mk Γ Δ) ℓ

end Propositional

end
