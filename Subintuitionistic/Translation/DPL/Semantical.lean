module

public import Subintuitionistic.Propositional.Coincide
public import Subintuitionistic.Translation.FPL
public import Subintuitionistic.Propositional.DPL.Kripke
public import Subintuitionistic.Modal.D.Kripke
public import Mathlib.Tactic.TFAE

/-!
# The embeddings of `𝐅𝐏𝐋`, `𝐒𝐏𝐋` and `𝐃𝐏𝐋` by Kripke semantics
-/

@[expose] public section

namespace Propositional.logicDPL.Derivable

open Modal

universe u

variable {α : Type u} [DecidableEq α] {ℓ : Fin 3} {Γ Δ : FormulaFinset α}

theorem iff_visser_semantical : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ ↔ ⊢ᴳ[𝐃] Γᵛ ⟹[ℓ] Δᵛ := by
  match ℓ with
  | 0 => exact iff_FPL.trans <| logicFPL.Derivable.iff_visser.trans logicD.Derivable.iff_GL.symm
  | 1 =>
    constructor
    · intro d;
      apply logicD.Derivable.complete₁;
      intro _ M _ s hs;
      exact (eventually_forces M.boxdotVal (s := ⟨s, hs⟩) d rfl).exists.imp fun _ ↦
        Model.boxdotVal_forcesSequent_iff.mp
    · intro d;
      apply ((level₁_TFAE (Γ := Γ) (Δ := Δ)).out 1 3).mpr;
      intro _ K _ s;
      exact (logicD.Derivable.eventually_forces K.toModal s.rel_succ d rfl).exists.imp fun _ ↦
          Propositional.Model.toModal_forcesSequent_visser_iff.mp
  | 2 =>
    constructor
    · intro d
      apply logicD.Derivable.complete₂;
      intro _ M _ r s hs hsr;
      exact Model.boxdotVal_forcesSequent_iff.mp
        (forces_of_level₂ M.boxdotVal (s := ⟨s, hs⟩) ⟨hsr.rel, hsr.eventually_rel⟩ d rfl)
    · intro d;
      apply ((level₂_TFAE (Γ := Γ) (Δ := Δ)).out 1 2).mpr;
      intro _ K _ s r hsr;
      exact Propositional.Model.toModal_forcesSequent_visser_iff.mp
          (logicD.Derivable.forces_of_level₂ K.toModal s.rel_succ
            ⟨hsr.rel, hsr.eventually_rel⟩ d rfl)

end Propositional.logicDPL.Derivable

namespace Propositional

open Modal Filter

universe u

variable {α : Type u} [DecidableEq α] {A : Formula α}

theorem mem_logicSPL_TFAE : [
    A ∈ 𝐒𝐏𝐋,
    Aᵛ ∈ 𝐒,
    ∀ {κ : Type u} (M : Propositional.Model κ α) [M.IsFPL] (s : M.InfiniteDescendingChain),
      ∀ᶠ n in atTop, s n ⊩[M] A,
    ∀ {κ : Type u} (M : Propositional.Model κ α) [M.IsFPL] (s : M.InfiniteDescendingChain),
      ∃ n, s n ⊩[M] A,
    ∀ {κ : Type u} (M : Propositional.Model κ α) [M.IsFiniteFPL] (t : M.World) (V : α → Prop),
      ∃ n : ℕ, Sum.inr (n : ℕ∞) ⊩[M.ωExtension t V] A,
    ∀ {κ : Type u} (M : Modal.Model κ α) [M.IsGL] (s : ℕ → M.World),
      (∀ n, M.Rel (s (n + 1)) (s n)) → ∀ᶠ n in atTop, s n ⊩[M] Aᵛ
  ].TFAE := by
  have h := logicDPL.Derivable.level₁_TFAE (Γ := ∅) (Δ := {A})
  tfae_have 1 ↔ 2 := by
    simpa [logicSPL, logicS] using
      logicDPL.Derivable.iff_visser_semantical (Γ := ∅) (Δ := {A}) (ℓ := 1)
  tfae_have 1 ↔ 3 := by
    have h₁ := h.out 1 2
    simpa [logicSPL, Model.World.ForcesSequent] using h₁
  tfae_have 1 ↔ 4 := by
    have h₁ := h.out 1 3
    simpa [logicSPL, Model.World.ForcesSequent] using h₁
  tfae_have 1 ↔ 5 := by
    have h₁ := h.out 1 5
    simpa [logicSPL, Model.World.ForcesSequent] using h₁
  tfae_have 2 → 6 := fun d _ M _ s hs ↦ by
    simpa [Modal.Model.World.ForcesSequent] using logicD.Derivable.eventually_forces M hs d rfl
  tfae_have 6 → 2 := fun h ↦ logicD.Derivable.complete₁ fun M _ s hs ↦ by
    simpa [Modal.Model.World.ForcesSequent] using (h M s hs).exists
  tfae_finish

theorem mem_logicDPL_TFAE : [
    A ∈ 𝐃𝐏𝐋,
    Aᵛ ∈ 𝐃,
    ∀ {κ : Type u} (M : Propositional.Model κ α) [M.IsFPL] (s : M.InfiniteDescendingChain)
      (r : M.World), s.ConvergesTo r → r ⊩[M] A,
    ∀ {κ : Type u} (M : Propositional.Model κ α) [M.IsFiniteFPL] (t : M.World) (V : α → Prop),
      Sum.inr ⊤ ⊩[M.ωExtension t V] A,
    ∀ {κ : Type u} (M : Modal.Model κ α) [M.IsGL] (r : M.World) (s : ℕ → M.World),
      (∀ n, M.Rel (s (n + 1)) (s n)) → M.ConvergesTo s r → r ⊩[M] Aᵛ
  ].TFAE := by
  have h := logicDPL.Derivable.level₂_TFAE (Γ := ∅) (Δ := {A})
  tfae_have 1 ↔ 2 := by
    simpa [logicDPL, logicD] using
      logicDPL.Derivable.iff_visser_semantical (Γ := ∅) (Δ := {A}) (ℓ := 2)
  tfae_have 1 ↔ 3 := by
    have h₁ := h.out 1 2
    simpa [logicDPL, Model.World.ForcesSequent] using h₁
  tfae_have 1 ↔ 4 := by
    have := h.out 1 4
    simpa [logicDPL, Model.World.ForcesSequent] using this
  tfae_have 2 → 5 := fun d _ M _ r s hs hsr ↦ by
    simpa [Modal.Model.World.ForcesSequent] using logicD.Derivable.forces_of_level₂ M hs hsr d rfl
  tfae_have 5 → 2 := fun h ↦ logicD.Derivable.complete₂ fun M _ r s hs hsr ↦ by
    simpa [Modal.Model.World.ForcesSequent] using h M r s hs hsr
  tfae_finish

/-- - [Nog26] -/
theorem visser_mem_TFAE : [Aᵛ ∈ 𝐆𝐋, Aᵛ ∈ 𝐃, Aᵛ ∈ 𝐒].TFAE := by
  have := (mem_logicFPL_TFAE (A := A)).out 1 3
  have := Set.ext_iff.mp logicFPL_eq_logicDPL A
  have := Set.ext_iff.mp logicDPL_eq_logicSPL A
  have := (mem_logicDPL_TFAE (A := A)).out 1 2
  have := (mem_logicSPL_TFAE (A := A)).out 1 2
  tfae_have 1 ↔ 2 := by tauto
  tfae_have 1 ↔ 3 := by tauto
  tfae_finish

end Propositional

end
