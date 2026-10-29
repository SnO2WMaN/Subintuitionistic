module

public import Subintuitionistic.Translation.Visser
public import Subintuitionistic.Propositional.DPL.Basic
public import Subintuitionistic.Modal.D.Kripke

/-!
# The embedding of `DPL` into `D`

`logicDPL.Derivable.iff_visser` is proved from `visser` and `of_visser`. It gives
`mem_logicSPL_iff`, `mem_logicDPL_iff` and the admissibility of `cut` for `⊢ᴳ[𝐃𝐏𝐋]`.
-/

@[expose] public section

namespace Translation

open Modal
open Propositional.logicFPL (imps exists_imps)

variable {α : Type*} [DecidableEq α] {Γ : Propositional.FormulaFinset α} {Φ₁ Φ₂ : Finset α}
  {Δ Θ : FormulaFinset α} {C : Formula α}

/-- - [Nog26, Lemmas 5.2, 8.2] -/
lemma persist (A : Propositional.Formula α) (ℓ : Fin 3) : ⊢ᴳ[𝐃] {Aᵛ} ⟹[ℓ] {□Aᵛ} := by
  induction A with
  | atom a =>
    have d : ⊢ᴳ[𝐃] FormulaFinset.box {#a} ∪ {#a} ⟹[0] {#a ⋏ □#a} :=
      .andR (Δ := ∅) (.union (A := #a) (by grind) (by grind))
        (.union (A := □#a) (by grind) (by grind))
    exact .andL (Γ := ∅) ((logicD.Derivable.boxK4 d ℓ).wk (by grind) (by grind))
  | falsum => exact logicD.Derivable.botL_mem (by grind)
  | and B C ihB ihC =>
    have h : ∀ x ∈ ({Bᵛ, Cᵛ} : FormulaFinset α), ⊢ᴳ[𝐃] {x} ⟹[ℓ] {□x} := by grind
    have d : ⊢ᴳ[𝐃] FormulaFinset.box {Bᵛ, Cᵛ} ∪ {Bᵛ, Cᵛ} ⟹[0] {Bᵛ ⋏ Cᵛ} :=
      .andR (Δ := ∅) (.union (A := Bᵛ) (by grind) (by grind))
        (.union (A := Cᵛ) (by grind) (by grind))
    exact .andL (Γ := ∅) ((logicD.Derivable.box_of_persist h d).wk (by grind) (by grind))
  | or B C ihB ihC =>
    have dB : ⊢ᴳ[𝐃] FormulaFinset.box {Bᵛ} ∪ {Bᵛ} ⟹[0] {Bᵛ ⋎ Cᵛ} :=
      .orR (Δ := ∅) (.union (A := Bᵛ) (by grind) (by grind))
    have dC : ⊢ᴳ[𝐃] FormulaFinset.box {Cᵛ} ∪ {Cᵛ} ⟹[0] {Bᵛ ⋎ Cᵛ} :=
      .orR (Δ := ∅) (.union (A := Cᵛ) (by grind) (by grind))
    exact .orL (Γ := ∅) (logicD.Derivable.box_of_persist (by grind) dB)
      (logicD.Derivable.box_of_persist (by grind) dC)
  | imp B C _ _ =>
    have d : ⊢ᴳ[𝐃] FormulaFinset.box {Bᵛ 🡒 Cᵛ} ∪ {Bᵛ 🡒 Cᵛ} ⟹[0] {□(Bᵛ 🡒 Cᵛ)} :=
      .union (A := □(Bᵛ 🡒 Cᵛ)) (by grind) (by grind)
    exact (logicD.Derivable.boxK4 (Γ := {Bᵛ 🡒 Cᵛ}) d ℓ).wk (by grind) (by grind)

/-- - [Nog26, Lemma 5.3] -/
lemma box_intro (d : ⊢ᴳ[𝐃] Γᵛ ∪ insert (□C) Δ ⟹[0] {C}) : ⊢ᴳ[𝐃] Γᵛ ∪ Δ.box ⟹[0] {□C} := by
  have d₁ : ⊢ᴳ[𝐃] insert (□C) ((Γᵛ ∪ Δ).box ∪ (Γᵛ ∪ Δ)) ⟹[0] {C} := d.wk (by grind) (by grind)
  have d₂ : ⊢ᴳ[𝐃] Γᵛ.box ∪ Δ.box ⟹[0] {□C} := d₁.boxGL.wk (by grind) (by grind)
  exact (logicD.Derivable.unbox_of_persist (fun B hB ↦ by grind [persist]) d₂).wk (by grind)
    (by grind)

open Propositional in
/-- - [Nog26, Lemma 8.4] -/
lemma var1 (a : α) : ⊢ᴳ[𝐃] {□#a} ⟹[1] {(#a)ᵛ} :=
  .andR (Δ := ∅) (.boxL (Γ := ∅) (.refl 1 #a)) (.refl 1 (□#a))

open Propositional in
/-- - [Nog26, Lemma 8.5] -/
lemma var2 (a : α) : ⊢ᴳ[𝐃] {(#a)ᵛ} ⟹[2] {□#a} :=
  .andL (Γ := ∅) ((logicD.Derivable.refl 2 (□#a)).wk (by grind) (by grind))

@[grind =] lemma visser_erase_bot : (Γ.erase ⊥)ᵛ = Γᵛ.erase ⊥ := by
  ext x
  grind

lemma exists_imps_of_box_subset (hΓ : Θ.box ⊆ Γᵛ ∪ Φ₁.image (#·) ∪ Φ₂.image (□#·)) :
    ∃ P, imps P ⊆ Γ ∧ P.image (fun p ↦ p.1ᵛ 🡒 p.2ᵛ) ⊆ Θ ∧
      Θ ⊆ P.image (fun p ↦ p.1ᵛ 🡒 p.2ᵛ) ∪ Φ₂.image (#·) := by
  obtain ⟨P, hP₁, hP₂⟩ := exists_imps Γ
  have hP : imps (P.filter fun p ↦ p.1ᵛ 🡒 p.2ᵛ ∈ Θ) ⊆ imps P :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  use P.filter fun p ↦ p.1ᵛ 🡒 p.2ᵛ ∈ Θ
  and_intros
  · exact hP.trans hP₁
  · grind
  · intro y hy
    have := hΓ (Finset.mem_image_of_mem _ hy)
    grind [Finset.mem_image_of_mem]

end Translation

namespace Propositional.logicDPL.Derivable

open Modal Translation

variable {α : Type*} [DecidableEq α] {ℓ : Fin 3} {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ : FormulaFinset α}
  {A : Formula α} {Φ₁ Φ₂ Ψ : Finset α}

/-! ### The forward direction -/

/-- - [Nog26, Lemmas 5.4, 8.7] -/
theorem visser (d : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ) : ⊢ᴳ[𝐃] Γᵛ ⟹[ℓ] Δᵛ := by
  generalize hS : (Γ ⟹[ℓ] Δ) = S at d
  induction d generalizing Γ Δ ℓ with cases hS
  | axm ℓ a =>
    simpa using logicD.Derivable.refl ℓ (#a)ᵛ
  | botL ℓ =>
    exact logicD.Derivable.botL_mem (by simp)
  | wk _ hΓ hΔ ih =>
    exact (ih rfl).wk (Finset.image_subset_image hΓ) (Finset.image_subset_image hΔ)
  | andL _ ih =>
    simpa [Formula.visser] using logicD.Derivable.andL (by simpa using ih rfl)
  | andR _ _ ih₁ ih₂ =>
    simpa [Formula.visser] using
      logicD.Derivable.andR (by simpa using ih₁ rfl) (by simpa using ih₂ rfl)
  | orL _ _ ih₁ ih₂ =>
    simpa [Formula.visser] using
      logicD.Derivable.orL (by simpa using ih₁ rfl) (by simpa using ih₂ rfl)
  | orR _ ih =>
    simpa [Formula.visser] using logicD.Derivable.orR (by simpa using ih rfl)
  | impL _ _ ih₁ ih₂ =>
    have := logicD.Derivable.impL (by simpa using ih₁ rfl) (by simpa using ih₂ rfl)
    simpa [Formula.visser] using this.boxL
  | @impR Θ A₁ A₂ P _ ih =>
    have h₁ := logicD.Derivable.impL_image (f := fun p ↦ p.1ᵛ) (g := fun p ↦ p.2ᵛ) (P := P)
      (Γ := insert (A₁ 🡒 A₂)ᵛ (insert A₁ᵛ Θᵛ)) (Δ := {A₂ᵛ}) fun I hI ↦
        (ih I hI rfl).wk (by simp [Finset.union_comm]) (by simp)
    have h₂ := logicD.Derivable.impR (A := A₁ᵛ) (B := A₂ᵛ) (Δ := ∅)
      (Γ := Θᵛ ∪ insert (□(A₁ᵛ 🡒 A₂ᵛ)) (P.image fun p ↦ p.1ᵛ 🡒 p.2ᵛ))
      (h₁.wk (by grind) (by grind))
    exact (box_intro (Γ := Θ) h₂).wk (by simp) (by simp [Formula.visser])
  | liftUp₀₁ _ ih =>
    exact (ih rfl).liftUp₀₁
  | @liftUp₁₂ P Q Φ _ ih =>
    have h₁ : ⊢ᴳ[𝐃] Φ.image (fun a ↦ (#a)ᵛ) ∪ P.image (fun p ↦ □(p.1ᵛ 🡒 p.2ᵛ)) ⟹[1]
        Q.image fun p ↦ □(p.1ᵛ 🡒 p.2ᵛ) := by
      simpa [Finset.union_comm] using ih rfl
    have h₂ := logicD.Derivable.replace_ant (g := fun a ↦ □#a) (fun a _ ↦ var1 a) h₁
    have h₃ := logicD.Derivable.liftUp₁₂ (Γ := (P.image fun p ↦ p.1ᵛ 🡒 p.2ᵛ) ∪ Φ.image (#·))
      (Δ := Q.image fun p ↦ p.1ᵛ 🡒 p.2ᵛ) (h₂.wk (by simp [Finset.union_comm]) (by simp))
    have h₄ := logicD.Derivable.replace_ant (S := Φ) (f := fun a ↦ □#a) (g := fun a ↦ (#a)ᵛ)
      (fun a _ ↦ var2 a) (Θ := P.image fun p ↦ □(p.1ᵛ 🡒 p.2ᵛ))
      (Δ := Q.image fun p ↦ □(p.1ᵛ 🡒 p.2ᵛ)) (h₃.wk (by simp [Finset.union_comm]) (by simp))
    simpa [Finset.union_comm] using h₄

/-! ### The backward direction -/

/-- - [Nog26, Lemmas 5.5, 8.8] -/
theorem of_visser (d : ⊢ᴳ[𝐃] Γᵛ ∪ Φ₁.image (#·) ∪ Φ₂.image (□#·) ⟹[ℓ] Ψ.image (#·) ∪ Δᵛ) :
    ⊢ᴳ[𝐃𝐏𝐋] Γ ∪ Φ₁.image (#·) ∪ Φ₂.image (#·) ⟹[ℓ] Ψ.image (#·) ∪ Δ := by
  obtain ⟨D⟩ := d
  generalize hΓ : (Γᵛ ∪ Φ₁.image (#·) ∪ Φ₂.image (□#·) : Modal.FormulaFinset α) = Θ at D
  generalize hΔ : (Ψ.image (#·) ∪ Δᵛ : Modal.FormulaFinset α) = Ξ at D
  generalize hS : (Θ ⟹[ℓ] Ξ) = S at D
  replace hΓ := hΓ.symm.subset
  replace hΔ := hΔ.symm.subset
  induction D using logicD.Derivation.height_induction generalizing Θ Ξ ℓ Γ Δ Φ₁ Φ₂ Ψ with cases hS
  | axm ℓ a => exact union (by grind) (by grind) ⟨a, rfl⟩
  | botL ℓ =>
    obtain ⟨E, hE, hE'⟩ : ∃ E ∈ Γ, Eᵛ = ⊥ := by simpa using hΓ
    exact botL_mem (by grind)
  | wk _ hΓ' hΔ' ih =>
    exact ih _ _ rfl (hΓ'.trans hΓ) (hΔ'.trans hΔ)
  | @impL ℓ Θ Ξ B C D₁ D₂ ih =>
    obtain ⟨E, hE, hEBC⟩ : ∃ E ∈ Γ, Eᵛ = B 🡒 C := by simpa using hΓ (Finset.mem_insert_self _ _)
    rcases visser_eq_imp.mp hEBC with ⟨a, rfl, rfl, rfl⟩ | ⟨A₁, A₂, rfl, rfl, rfl⟩ |
      ⟨A₁, A₂, rfl, rfl, rfl⟩
    · obtain ⟨D₃, h₃⟩ := D₁.invImpR (Finset.mem_insert_self _ _)
      obtain ⟨D₄, h₄⟩ := D₃.invImpR (Finset.mem_insert_self _ _)
      obtain ⟨D, h⟩ := D₄.erase_bot
      replace ih := ih D (by omega) (Γ := Γ) (Δ := Δ.erase ⊥) (Φ₁ := insert a Φ₁)
        (Φ₂ := insert a Φ₂) (Ψ := Ψ) _ _ rfl
      replace ih := ih (fun x _ ↦ by have := @hΓ x; grind) (fun x _ ↦ by have := @hΔ x; grind)
      exact ih.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind)
    · obtain ⟨D₃, h₃⟩ := D₁.invImpR (Finset.mem_insert_self _ _)
      obtain ⟨D₄, h₄⟩ := D₃.invImpR (Finset.mem_insert_self _ _)
      obtain ⟨D, h⟩ := D₄.erase_bot
      replace ih := ih D (by omega) (Γ := insert A₁ (insert A₂ Γ)) (Δ := Δ.erase ⊥) (Φ₁ := Φ₁)
        (Φ₂ := Φ₂) (Ψ := Ψ) _ _ rfl
      replace ih := ih (fun x _ ↦ by have := @hΓ x; grind) (fun x _ ↦ by have := @hΔ x; grind)
      exact andL_of_mem (A := A₁) (B := A₂) (by grind)
        (ih.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind))
    · obtain ⟨D₃, h₃⟩ := D₁.invImpR (Finset.mem_insert_self _ _)
      obtain ⟨D, h⟩ := D₃.erase_bot
      have h₁ := ih D (by omega) (Γ := insert A₁ Γ) (Δ := Δ.erase ⊥) (Φ₁ := Φ₁) (Φ₂ := Φ₂)
        (Ψ := Ψ) _ _ rfl
      replace ih := ih D₂ (le_max_right _ _) (Γ := insert A₂ Γ) (Δ := Δ) (Φ₁ := Φ₁) (Φ₂ := Φ₂)
        (Ψ := Ψ) _ _ rfl
      replace h₁ := h₁ (fun x _ ↦ by have := @hΓ x; grind) (fun x _ ↦ by have := @hΔ x; grind)
      replace ih := ih (fun x _ ↦ by have := @hΓ x; grind) hΔ
      exact orL_of_mem (A := A₁) (B := A₂) (by grind)
        (h₁.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind))
        (ih.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind))
  | @impR ℓ Θ Ξ B C D ih =>
    obtain ⟨E, hE, hEBC⟩ : ∃ E ∈ Δ, Eᵛ = B 🡒 C := by simpa using hΔ (Finset.mem_insert_self _ _)
    rcases visser_eq_imp.mp hEBC with ⟨a, rfl, rfl, rfl⟩ | ⟨A₁, A₂, rfl, rfl, rfl⟩ |
      ⟨A₁, A₂, rfl, rfl, rfl⟩
    · obtain ⟨D₁, h₁⟩ := D.invImpL_left (Finset.mem_insert_self _ _)
      obtain ⟨D₂, h₂⟩ := D₁.erase_bot
      replace ih := ih D₂ (by omega) (Γ := Γ) (Δ := Δ.erase ⊥) (Φ₁ := Φ₁) (Φ₂ := Φ₂)
        (Ψ := insert a Ψ) _ _ rfl
      replace ih := ih (fun x _ ↦ by have := @hΓ x; grind) (fun x _ ↦ by have := @hΔ x; grind)
      exact ih.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind)
    · obtain ⟨D₁, h₁⟩ := D.invImpL_left (Finset.mem_insert_self _ _)
      obtain ⟨D₂, h₂⟩ := D.invImpL_right (Finset.mem_insert_self _ _)
      obtain ⟨D₃, h₃⟩ := D₁.erase_bot
      obtain ⟨D₄, h₄⟩ := D₂.invImpL_left (Finset.mem_insert_self _ _)
      obtain ⟨D₅, h₅⟩ := D₄.erase_bot
      have h₆ := ih D₃ (by omega) (Γ := Γ) (Δ := insert A₁ (Δ.erase ⊥)) (Φ₁ := Φ₁) (Φ₂ := Φ₂)
        (Ψ := Ψ) _ _ rfl
      replace ih := ih D₅ (by omega) (Γ := Γ) (Δ := insert A₂ (Δ.erase ⊥)) (Φ₁ := Φ₁)
        (Φ₂ := Φ₂) (Ψ := Ψ) _ _ rfl
      replace h₆ := h₆ (fun x _ ↦ by have := @hΓ x; grind) (fun x _ ↦ by have := @hΔ x; grind)
      replace ih := ih (fun x _ ↦ by have := @hΓ x; grind) (fun x _ ↦ by have := @hΔ x; grind)
      exact andR_of_mem (A := A₁) (B := A₂) (by grind)
        (h₆.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind))
        (ih.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind))
    · obtain ⟨D₁, h₁⟩ := D.invImpL_left (Finset.mem_insert_self _ _)
      replace ih := ih D₁ h₁ (Γ := Γ) (Δ := insert A₁ (insert A₂ Δ)) (Φ₁ := Φ₁) (Φ₂ := Φ₂)
        (Ψ := Ψ) _ _ rfl
      replace ih := ih (fun x _ ↦ by have := @hΓ x; grind) (fun x _ ↦ by have := @hΔ x; grind)
      exact orR_of_mem (A := A₁) (B := A₂) (by grind)
        (ih.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind))
  | @boxGL Θ B D ih =>
    obtain ⟨A₁, A₂, h, rfl⟩ : ∃ A₁ A₂ : Formula α, A₁ 🡒 A₂ ∈ Δ ∧ B = A₁ᵛ 🡒 A₂ᵛ := by grind
    obtain ⟨P, hP₁, hP₂, hP₃⟩ := exists_imps_of_box_subset hΓ
    apply impR_of_mem (P := P) (A := A₁) (B := A₂) (by grind) (by grind)
    intro I hI
    have hinj : Function.Injective fun p : Formula α × Formula α ↦ p.1ᵛ 🡒 p.2ᵛ :=
      fun p q e ↦ by grind [visser_injective.eq_iff]
    obtain ⟨D₁, h₁⟩ := D.invImpR (Finset.mem_singleton_self _)
    obtain ⟨D₂, h₂⟩ := D₁.invImps (f := fun p ↦ p.1ᵛ) (g := fun p ↦ p.2ᵛ) hinj
      (fun x _ ↦ by grind) hI
    have hI₁ : I.image (fun p : Formula α × Formula α ↦ p.2ᵛ) = (I.image Prod.snd)ᵛ :=
      Finset.image_image.symm
    have hI₂ : (P \ I).image (fun p : Formula α × Formula α ↦ p.1ᵛ) = ((P \ I).image Prod.fst)ᵛ :=
      Finset.image_image.symm
    have hv : (A₁ 🡒 A₂)ᵛ = □(A₁ᵛ 🡒 A₂ᵛ) := rfl
    replace ih := ih D₂ (by omega) (Γ := insert A₁ (insert (A₁ 🡒 A₂) (Γ ∪ I.image Prod.snd)))
      (Δ := insert A₂ ((P \ I).image Prod.fst)) (Φ₁ := Φ₁ ∪ Φ₂) (Φ₂ := Φ₂) (Ψ := ∅) _ _ rfl
    replace ih := ih
      (fun x _ ↦ by have := @hΓ x; have := @hP₃ x; grind [Finset.image_union])
      (fun x _ ↦ by grind)
    exact ih.wk (fun x _ ↦ by grind [Finset.image_union]) (fun x _ ↦ by grind)
  | @boxL Θ Ξ B D ih =>
    obtain ⟨E, hE, hEB⟩ | ⟨a, ha, ⟨⟩⟩ : (∃ E ∈ Γ, Eᵛ = □B) ∨ ∃ a ∈ Φ₂, □#a = □B := by
      simpa using hΓ (Finset.mem_insert_self _ _)
    · obtain ⟨A₁, A₂, rfl, rfl⟩ := visser_eq_box.mp hEB
      obtain ⟨D₁, h₁⟩ := D.invImpL_left (Finset.mem_insert_self _ _)
      obtain ⟨D₂, h₂⟩ := D.invImpL_right (Finset.mem_insert_self _ _)
      have h₃ := ih D₁ h₁ (Γ := Γ) (Δ := insert A₁ Δ) (Φ₁ := Φ₁) (Φ₂ := Φ₂) (Ψ := Ψ) _ _ rfl
      replace ih := ih D₂ h₂ (Γ := insert A₂ Γ) (Δ := Δ) (Φ₁ := Φ₁) (Φ₂ := Φ₂) (Ψ := Ψ) _ _ rfl
      replace h₃ := h₃ (fun x _ ↦ by have := @hΓ x; grind) (fun x _ ↦ by have := @hΔ x; grind)
      replace ih := ih (fun x _ ↦ by have := @hΓ x; grind) hΔ
      exact impL_of_mem (A := A₁) (B := A₂) (by grind)
        (h₃.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind))
        (ih.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind))
    · replace ih := ih D le_rfl (Γ := Γ) (Δ := Δ) (Φ₁ := insert a Φ₁) (Φ₂ := Φ₂) (Ψ := Ψ) _ _ rfl
      replace ih := ih (fun x _ ↦ by have := @hΓ x; grind) hΔ
      exact ih.wk (fun x _ ↦ by grind) subset_rfl
  | liftUp₀₁ D ih =>
    exact liftUp₀₁ (ih D le_rfl _ _ rfl hΓ hΔ)
  | liftUp₁₂ D ih =>
    obtain ⟨P, hP₁, hP₂⟩ := logicFPL.exists_imps Γ
    obtain ⟨Q, hQ₁, hQ₂⟩ := logicFPL.exists_imps Δ
    replace ih := ih D le_rfl (Γ := logicFPL.imps P) (Δ := logicFPL.imps Q) (Φ₁ := ∅)
      (Φ₂ := Φ₂) (Ψ := ∅) _ _ rfl
    replace ih := ih (fun x _ ↦ by have := @hΓ x; grind) (fun x _ ↦ by have := @hΔ x; grind)
    have h₂ := liftUp₁₂ (P := P) (Q := Q) (Φ := Φ₂)
      (ih.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind))
    exact h₂.wk (fun x _ ↦ by grind) (fun x _ ↦ by grind)

/-! ### The embedding and its corollaries -/

/-- - [Nog26, Theorems 5.7, 8.10] -/
theorem iff_visser : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ ↔ ⊢ᴳ[𝐃] Γᵛ ⟹[ℓ] Δᵛ := by
  constructor
  · exact visser
  · intro d
    simpa using of_visser (Φ₁ := ∅) (Φ₂ := ∅) (Ψ := ∅) (by simpa using d)

/-- - [Nog26, Corollaries 5.9, 8.12] -/
theorem cut (h₁ : ⊢ᴳ[𝐃𝐏𝐋] Γ₁ ⟹[ℓ] insert A Δ₁) (h₂ : ⊢ᴳ[𝐃𝐏𝐋] insert A Γ₂ ⟹[ℓ] Δ₂) :
    ⊢ᴳ[𝐃𝐏𝐋] Γ₁ ∪ Γ₂ ⟹[ℓ] Δ₁ ∪ Δ₂ := by
  replace h₁ : ⊢ᴳ[𝐃] Γ₁ᵛ ⟹[ℓ] insert Aᵛ Δ₁ᵛ := by simpa using visser h₁
  replace h₂ : ⊢ᴳ[𝐃] insert Aᵛ Γ₂ᵛ ⟹[ℓ] Δ₂ᵛ := by simpa using visser h₂
  exact iff_visser.mpr (by simpa using .cut h₁ h₂)

end Propositional.logicDPL.Derivable

namespace Propositional

open Modal

variable {α : Type*} [DecidableEq α] {A : Formula α}

/-- - [Nog26, Corollary 5.8] -/
theorem mem_logicSPL_iff : A ∈ 𝐒𝐏𝐋 ↔ Aᵛ ∈ 𝐒 := by
  simpa [logicSPL, logicS] using logicDPL.Derivable.iff_visser (Γ := ∅) (Δ := {A}) (ℓ := 1)

/-- - [Nog26, Corollary 8.11] -/
theorem mem_logicDPL_iff : A ∈ 𝐃𝐏𝐋 ↔ Aᵛ ∈ 𝐃 := by
  simpa [logicDPL, logicD] using logicDPL.Derivable.iff_visser (Γ := ∅) (Δ := {A}) (ℓ := 2)

end Propositional

end
