module

public import Subintuitionistic.Propositional.DPL.Kripke

/-!
# Separation of the levels and the coincidence of `𝐅𝐏𝐋`, `𝐒𝐏𝐋` and `𝐃𝐏𝐋`
-/

@[expose] public section

namespace Propositional

universe u

namespace Model

/-- The model with one point without successors. -/
def singleton {α : Type*} (V : α → Prop) : Model PUnit.{u + 1} α where
  Rel' _ _ := False
  Val' _ := V
  hereditary' := fun h ↦ h.elim

instance {α : Type*} (V : α → Prop) : (singleton.{u} V).IsFiniteFPL where
  trans _ _ _ h := h.elim
  irrefl _ h := h

end Model

namespace logicDPL.Derivable

open Model Model.World
open FormulaFinset (imps)

variable {α : Type u} [DecidableEq α] {Γ Δ : FormulaFinset α}

/-- - [Nog26] -/
theorem level₂_of_level₀ (d : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[0] Δ) : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[2] Δ := by
  have h := (level₀_TFAE (Γ := Γ) (Δ := Δ)).out 1 3 |>.mp d
  apply ((level₂_TFAE (Γ := Γ) (Δ := Δ)).out 3 1).mp
  intro _ M _ t V
  exact h (M.ωExtension t V) _

/-- - [Nog26] -/
theorem level₁_of_level₂ (d : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[2] Δ) : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[1] Δ := by
  suffices ∀ {S : LayeredSequent α}, ⊢ᴳ[𝐃𝐏𝐋] S → S.level = 2 → ⊢ᴳ[𝐃𝐏𝐋] S.ant ⟹[1] S.suc from
    this d rfl
  intro S h hS
  induction h with
  | axm => exact axm 1 _
  | botL => exact botL 1
  | wk _ hΓ hΔ ih => exact (ih hS).wk hΓ hΔ
  | andL _ ih => exact (ih hS).andL
  | andR _ _ ih₁ ih₂ => exact (ih₁ hS).andR (ih₂ hS)
  | orL _ _ ih₁ ih₂ => exact (ih₁ hS).orL (ih₂ hS)
  | orR _ ih => exact (ih hS).orR
  | liftUp₁₂ d => exact d
  | impL | impR | liftUp₀₁ => nomatch hS

/-- - [Nog26] -/
theorem not_level₀_of_imps_of_atoms (hΓ : ∀ C ∈ Γ, ∃ A B, C = A 🡒 B)
    (hΔ : ∀ D ∈ Δ, ∃ a, D = #a) : ⊬ᴳ[𝐃𝐏𝐋] Γ ⟹[0] Δ := by
  intro d
  have h := ((level₀_TFAE (Γ := Γ) (Δ := Δ)).out 1 4).mp d
  obtain ⟨D, hD, hxD⟩ := h (singleton.{u} fun _ ↦ False) PUnit.unit fun C hC ↦ by
    obtain ⟨A, B, rfl⟩ := hΓ C hC
    exact fun y Rxy ↦ Rxy.elim
  obtain ⟨a, rfl⟩ := hΔ D hD
  exact hxD

lemma level₀_top : ⊢ᴳ[𝐃𝐏𝐋] (∅ : FormulaFinset α) ⟹[0] {⊤} := by
  have := impR (Θ := ∅) (P := ∅) (A := ⊥) (B := (⊥ : Formula α)) fun I _ ↦ botL_mem (by simp)
  simpa [imps] using this

/-- - [Nog26] -/
theorem level₂_not_level₀ :
    ⊢ᴳ[𝐃𝐏𝐋] ({∼⊤} : FormulaFinset α) ⟹[2] ∅ ∧
      ⊬ᴳ[𝐃𝐏𝐋] ({∼⊤} : FormulaFinset α) ⟹[0] ∅ := by
  constructor
  · have h : ⊢ᴳ[𝐃𝐏𝐋] ({∼⊤} : FormulaFinset α) ⟹[1] ∅ := by
      have := impL (Γ := (∅ : FormulaFinset α)) (Δ := ∅) (A := ⊤) (B := ⊥)
        (by simpa using level₀_top.liftUp₀₁) (botL_mem (by simp))
      simpa using this
    have := liftUp₁₂ (P := {(⊤, ⊥)}) (Q := ∅) (Φ := ∅) (by simpa [imps] using h)
    simpa [imps] using this
  · exact not_level₀_of_imps_of_atoms (by simp) (by simp)

/-- - [Nog26] -/
theorem level₁_not_level₂ (a : α) :
    ⊢ᴳ[𝐃𝐏𝐋] ({⊤ 🡒 #a} : FormulaFinset α) ⟹[1] {#a} ∧
      ⊬ᴳ[𝐃𝐏𝐋] ({⊤ 🡒 #a} : FormulaFinset α) ⟹[2] {#a} := by
  constructor
  · simpa using impL (Γ := ∅) (Δ := {#a}) (A := ⊤) (B := #a)
      (level₀_top.liftUp₀₁.wk (by simp) (by simp)) (axm_mem (by simp) (by simp) ⟨a, rfl⟩)
  · intro d
    have := ((level₂_TFAE (Γ := {⊤ 🡒 #a}) (Δ := {#a})).out 1 4).mp d
    obtain ⟨D, hD, hxD⟩ :=
      this (singleton.{u} fun _ ↦ True) PUnit.unit (fun _ ↦ False) fun C hC ↦ by
        obtain rfl := Finset.mem_singleton.mp hC
        rintro (y | j) Rxy _
        · exact trivial
        · exact ⟨trivial, fun hj ↦ absurd Rxy (by simp [hj])⟩
    obtain rfl := Finset.mem_singleton.mp hD
    exact (show False from hxD.2 rfl)

end logicDPL.Derivable

open logicDPL.Derivable

variable {α : Type u} [DecidableEq α] {A : Formula α}

lemma mem_logicFPL_of_forces_ωExtension
    (h : ∀ {κ : Type u} (M : Model κ α) [M.IsFiniteFPL] (x : M.World),
      ∃ i : ℕ∞, Sum.inr i ⊩[M.ωExtension x fun a ↦ M x a] (∅ ⟹ {A})) : A ∈ 𝐅𝐏𝐋 := by
  apply logicFPL.Derivable.complete
  intro _ M _ x
  obtain ⟨i, hi⟩ := h M x
  obtain ⟨D, hD, hxD⟩ := hi (by simp)
  obtain rfl := Finset.mem_singleton.mp hD
  exact fun _ ↦ ⟨_, hD, Model.ωExtension.forces_of_forces_inr hxD⟩

lemma logicSPL_subset_logicFPL : (𝐒𝐏𝐋 : Logic α) ⊆ 𝐅𝐏𝐋 := by
  intro A h
  apply mem_logicFPL_of_forces_ωExtension
  intro _ M _ x
  have h' := ((level₁_TFAE (Γ := ∅) (Δ := {A})).out 1 5).mp h
  obtain ⟨n, hn⟩ := h' M x _
  exact ⟨n, hn⟩

lemma logicDPL_subset_logicFPL : (𝐃𝐏𝐋 : Logic α) ⊆ 𝐅𝐏𝐋 := by
  intro A h
  apply mem_logicFPL_of_forces_ωExtension
  intro _ M _ x
  have h' := ((level₂_TFAE (Γ := ∅) (Δ := {A})).out 1 4).mp h
  exact ⟨⊤, h' M x _⟩

/-- - [Nog26] -/
theorem logicFPL_eq_logicDPL : (𝐅𝐏𝐋 : Logic α) = 𝐃𝐏𝐋 := by
  apply Set.Subset.antisymm;
  · exact fun _ h ↦ level₂_of_level₀ (iff_FPL.mpr h)
  · exact logicDPL_subset_logicFPL

/-- - [Nog26] -/
theorem logicDPL_eq_logicSPL : (𝐃𝐏𝐋 : Logic α) = 𝐒𝐏𝐋 := by
  apply Set.Subset.antisymm;
  · exact fun _ ↦ level₁_of_level₂
  · rw [←logicFPL_eq_logicDPL];
    exact logicSPL_subset_logicFPL;

end Propositional

end
