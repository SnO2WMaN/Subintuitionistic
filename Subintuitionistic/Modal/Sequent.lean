module

public import Subintuitionistic.Modal.Formula
public import Subintuitionistic.ToMathlib.Order.Preorder.Finite

/-!
# Sequents of modal formulas

A sequent `Γ ⟹ Δ` is a pair of finite sets of formulas. `S ⊆ T` is inclusion side by side, so
`S ⊆ (Λ ⟹ Λ)` states that every formula of `S` is in `Λ`. A layered sequent `Γ ⟹[ℓ] Δ` is a
sequent with a level `ℓ : Fin 3`; the levels `0`, `1`, `2` belong to `GL`, `S` and `D`.
-/

@[expose] public section

namespace Modal

structure Sequent (α : Type*) where
  ant : FormulaFinset α
  suc : FormulaFinset α

scoped[Modal] infix:50 " ⟹ " => Sequent.mk

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
  have key : ∀ U, (Γ ⟹ Δ) ⊆ U → U ⊆ (Λ ⟹ Λ) → ¬P U → U = (Γ ⟹ Δ) := by
    intro U hU₁ hU₂ hU
    obtain ⟨e₁, e₂⟩ := hmax U.ant U.suc hU₁.1 hU₂.1 hU₁.2 hU₂.2 hU
    exact ext e₁ e₂
  exact ⟨Γ ⟹ Δ, ⟨h₁, h₃⟩, ⟨h₂, h₄⟩, h₅, key⟩

structure Saturated (S : Sequent α) : Prop where
  impL : ∀ {A B}, A 🡒 B ∈ S.ant → A ∈ S.suc ∨ B ∈ S.ant
  impR : ∀ {A B}, A 🡒 B ∈ S.suc → A ∈ S.ant ∧ B ∈ S.suc

attribute [grind →] Saturated.impL Saturated.impR

variable [DecidableEq α]

lemma saturated_of_maximal (P : Sequent α → Prop) (hΛ : Λ.SubformulaClosed)
    (hT : T ⊆ (Λ ⟹ Λ)) (hd : ¬P T) (hmax : ∀ U, T ⊆ U → U ⊆ (Λ ⟹ Λ) → ¬P U → U = T)
    (impL : ∀ {Γ Δ A B}, A 🡒 B ∈ Γ → P (Γ ⟹ insert A Δ) → P (insert B Γ ⟹ Δ) → P (Γ ⟹ Δ))
    (impR : ∀ {Γ Δ A B}, A 🡒 B ∈ Δ → P (insert A Γ ⟹ insert B Δ) → P (Γ ⟹ Δ)) :
    T.Saturated := by
  have key : ∀ U, T ⊆ U → U ⊆ (Λ ⟹ Λ) → U ⊆ T ∨ P U := by
    intro U h₁ h₂
    by_cases hU : P U
    · exact Or.inr hU
    · have e := hmax U h₁ h₂ hU
      exact Or.inl ⟨(congrArg Sequent.ant e).subset, (congrArg Sequent.suc e).subset⟩
  constructor
  · intro A B hAB
    have hAB' := hΛ.imp (hT.1 hAB)
    have h₁ := key (T.ant ⟹ insert A T.suc) (by grind) (by grind)
    have h₂ := key (insert B T.ant ⟹ T.suc) (by grind) (by grind)
    by_contra hc
    have d₁ : P (T.ant ⟹ insert A T.suc) := by grind
    have d₂ : P (insert B T.ant ⟹ T.suc) := by grind
    exact hd (impL hAB d₁ d₂)
  · intro A B hAB
    have hAB' := hΛ.imp (hT.2 hAB)
    obtain h | d := key (insert A T.ant ⟹ insert B T.suc) (by grind) (by grind)
    · grind
    · exact (hd (impR hAB d)).elim

@[grind]
def subfmls (S : Sequent α) : FormulaFinset α := (S.ant ∪ S.suc).subfmls

@[grind .] lemma subset_subfmls : S ⊆ (S.subfmls ⟹ S.subfmls) := by
  have h : S.ant ∪ S.suc ⊆ S.subfmls := FormulaFinset.subset_subfmls
  constructor <;> grind

@[grind .] lemma subformulaClosed_subfmls : S.subfmls.SubformulaClosed := by grind

end Sequent

/-- - [KKIM25] -/
structure LayeredSequent (α : Type*) extends Sequent α where
  level : Fin 3

scoped[Modal] notation:50 Γ:51 " ⟹[" ℓ "] " Δ:51 => LayeredSequent.mk (Sequent.mk Γ Δ) ℓ

end Modal

end
