module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Preorder.Finite

/-!
# Maximal pairs of finite sets

For a predicate `P` on pairs of finite subsets of `Λ`, a pair `(Γ, Δ)` with `¬P Γ Δ` extends to a
pair with `¬P` that no other such pair properly extends.
-/

@[expose] public section

namespace Finset

variable {β : Type*} {P : Finset β → Finset β → Prop} {Λ Γ Δ : Finset β}

lemma exists_maximal_pair (hΓ : Γ ⊆ Λ) (hΔ : Δ ⊆ Λ) (h : ¬P Γ Δ) :
    ∃ Γ' Δ', Γ ⊆ Γ' ∧ Γ' ⊆ Λ ∧ Δ ⊆ Δ' ∧ Δ' ⊆ Λ ∧ ¬P Γ' Δ' ∧
      ∀ Γ'' Δ'', Γ' ⊆ Γ'' → Γ'' ⊆ Λ → Δ' ⊆ Δ'' → Δ'' ⊆ Λ → ¬P Γ'' Δ'' →
        Γ'' = Γ' ∧ Δ'' = Δ' := by
  classical
  let X := (Λ.powerset ×ˢ Λ.powerset).filter fun p ↦ Γ ⊆ p.1 ∧ Δ ⊆ p.2 ∧ ¬P p.1 p.2
  have hX : (Γ, Δ) ∈ X := by simp [X, hΓ, hΔ, h]
  obtain ⟨⟨Γ', Δ'⟩, hm, hmax⟩ := X.exists_maximal ⟨_, hX⟩
  have hm' : (Γ' ⊆ Λ ∧ Δ' ⊆ Λ) ∧ Γ ⊆ Γ' ∧ Δ ⊆ Δ' ∧ ¬P Γ' Δ' := by simpa [X] using hm
  obtain ⟨⟨hΓ', hΔ'⟩, hΓΓ', hΔΔ', hP⟩ := hm'
  have key : ∀ Γ'' Δ'', Γ' ⊆ Γ'' → Γ'' ⊆ Λ → Δ' ⊆ Δ'' → Δ'' ⊆ Λ → ¬P Γ'' Δ'' →
      Γ'' = Γ' ∧ Δ'' = Δ' := by
    intro Γ'' Δ'' h₁ h₂ h₃ h₄ h₅
    have hmem : (Γ'', Δ'') ∈ X := by simp [X, h₂, h₄, hΓΓ'.trans h₁, hΔΔ'.trans h₃, h₅]
    obtain ⟨h₆, h₇⟩ := hmax hmem ⟨h₁, h₃⟩
    exact ⟨h₆.antisymm h₁, h₇.antisymm h₃⟩
  exact ⟨Γ', Δ', hΓΓ', hΓ', hΔΔ', hΔ', hP, key⟩

end Finset

end
