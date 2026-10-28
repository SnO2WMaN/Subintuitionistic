module

public import Subintuitionistic.Translation.Basic

/-!
# Semantics of the Visser translation

The FPL model `M.boxdotVal` of a GL model `M` and the GL model `K.toModal` of an FPL model `K`,
the forcing of `Aᵛ` in them, and the equivalence of validity of `Γ ⟹ A` in FPL models with
validity of `Γᵛ ⟹ Aᵛ` in GL models.

## References

- [Vis81, Theorem 5.4]
-/

@[expose] public section

open Propositional.Formula

namespace Modal.Model

variable {κ α : Type*} {M : Model κ α}

/-- The FPL model on the frame of `M` whose truth set of `p` is the truth set of `p ⋏ □p` in `M`.
- [Vis81, Theorem 5.4] -/
def boxdotVal (M : Model κ α) [IsTrans _ M.Rel] : Propositional.Model κ α where
  Rel' := M.Rel
  Val' x a := M x a ∧ ∀ y, M.Rel x y → M y a
  hereditary' Rxy _ := fun ⟨_, h⟩ ↦ ⟨h _ Rxy, fun z Ryz ↦ h z (_root_.trans Rxy Ryz)⟩

variable [M.IsFiniteGL]

@[simp, grind _=_] lemma boxdotVal_rel {x y : M.World} : M.boxdotVal.Rel x y ↔ M.Rel x y := Iff.rfl

@[simp, grind =] lemma boxdotVal_val {x : M.World} {a : α} :
    M.boxdotVal x a ↔ M x a ∧ ∀ y, x ≺ y → M y a := Iff.rfl

instance : M.boxdotVal.IsFPL where
  trans := IsTrans.trans (r := M.Rel)
  irrefl := Std.Irrefl.irrefl (r := M.Rel)
  finite := inferInstanceAs (Finite M.World)

open Propositional in
lemma boxdotVal_forces_iff {x : M.World} {A : Propositional.Formula α} :
    x ⊩[M.boxdotVal] A ↔ x ⊩ Aᵛ := by
  induction A generalizing x with
  | falsum | atom a | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB => grind

end Modal.Model

namespace Propositional.Model

variable {κ α : Type*}

/-- The GL model with the frame and the valuation of an FPL model `K`.
- [Vis81, Theorem 5.4] -/
def toModal (K : Model κ α) : Modal.Model κ α where
  Rel' := K.Rel
  Val' := K.Val

variable {K : Model κ α}

@[simp, grind =] lemma toModal_val {x : K.World} {a : α} : K.toModal x a ↔ K x a :=
  Iff.rfl

@[simp, grind _=_] lemma toModal_rel {x y : K.World} : K.toModal.Rel x y ↔ K.Rel x y := Iff.rfl

instance [K.IsFPL] : K.toModal.IsFiniteGL where
  trans := IsTrans.trans (r := K.Rel)
  irrefl := Std.Irrefl.irrefl (r := K.Rel)
  finite := inferInstanceAs (Finite K.World)

open Modal in
lemma toModal_forces_visser_iff [K.IsFPL] {x : K.World} {A : Formula α} :
    x ⊩[K.toModal] Aᵛ ↔ x ⊩ A := by
  induction A generalizing x with
  | atom a => grind
  | falsum | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB => grind

end Propositional.Model

namespace Translation

open Propositional Modal

universe u

variable {α : Type u} [DecidableEq α] {Γ : Propositional.FormulaFinset α}
  {A : Propositional.Formula α}

/-- `Γ ⟹ {A}` is valid in every FPL model if and only if `Γᵛ ⟹ {Aᵛ}` is valid in every GL model.
- [Vis81, Theorem 5.4] -/
theorem valid_iff_visser :
    (∀ {κ : Type u} (K : Propositional.Model κ α), [K.IsFPL] → K ⊧ Γ ⟹ {A}) ↔
    ∀ {κ : Type u} (M : Modal.Model κ α), [M.IsFiniteGL] → M ⊧ Γᵛ ⟹ {Aᵛ} := by
  constructor
  · intro h κ M _
    apply Modal.Model.validateSequent_singleton_iff.mpr
    intro x hΓ
    have h₁ := Propositional.Model.validateSequent_singleton_iff.mp (h M.boxdotVal) x
    grind [Modal.Model.boxdotVal_forces_iff]
  · intro h κ K _
    apply Propositional.Model.validateSequent_singleton_iff.mpr
    intro x hΓ
    have h₁ := Modal.Model.validateSequent_singleton_iff.mp (h K.toModal) x
    grind [Propositional.Model.toModal_forces_visser_iff]

end Translation

end
