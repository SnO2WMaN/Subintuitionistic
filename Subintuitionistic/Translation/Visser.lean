module

public import Subintuitionistic.Translation.Basic

/-!
# The Visser translation

The shape of `Aᵛ` (`visser_ne_atom`, `visser_eq_bot`, `visser_eq_box`, `visser_eq_imp`,
`visser_injective`), `Modal.Model.boxdotVal` and `Propositional.Model.toModal`, the forcing of `Aᵛ`
in them, and `valid_iff_visser`.

## References

- [Vis81, Theorem 5.4]
-/

@[expose] public section

open Propositional.Formula

/-! ### The syntax of the translation -/

namespace Translation

open Modal

variable {α : Type*} {A : Propositional.Formula α} {a : α} {B C : Modal.Formula α}

@[simp, grind .] lemma visser_ne_atom : Aᵛ ≠ #a := by
  cases A <;> simp [visser, Formula.and, Formula.or, Formula.neg]

@[simp, grind =] lemma visser_eq_bot : Aᵛ = ⊥ ↔ A = ⊥ := by
  cases A <;> simp [visser, Formula.and, Formula.or, Formula.neg]

lemma visser_eq_box : Aᵛ = □B ↔ ∃ C D, A = .imp C D ∧ B = Cᵛ 🡒 Dᵛ := by
  cases A <;> simp [visser, Formula.and, Formula.or, Formula.neg, eq_comm]

lemma visser_eq_imp :
    Aᵛ = B 🡒 C ↔ (∃ a, A = .atom a ∧ B = #a 🡒 ∼□#a ∧ C = ⊥) ∨
      (∃ D E, A = .and D E ∧ B = Dᵛ 🡒 ∼Eᵛ ∧ C = ⊥) ∨ (∃ D E, A = .or D E ∧ B = ∼Dᵛ ∧ C = Eᵛ) := by
  cases A <;> simp [visser, Formula.and, Formula.or, Formula.neg, eq_comm]

lemma visser_injective : Function.Injective (visser (α := α)) := by
  intro A B hAB
  induction A generalizing B with
  | atom a | falsum | and A₁ A₂ ih₁ ih₂ | or A₁ A₂ ih₁ ih₂ | imp A₁ A₂ ih₁ ih₂ =>
    cases B <;>
      simp [visser, Formula.and, Formula.or, Formula.neg] at hAB ⊢ <;> grind

variable [DecidableEq α] {Γ : Propositional.FormulaFinset α}

@[grind →] lemma exists_imp_of_box_mem_visser (h : □B ∈ Γᵛ) :
    ∃ C D, .imp C D ∈ Γ ∧ B = Cᵛ 🡒 Dᵛ := by
  obtain ⟨E, hE, hEB⟩ : ∃ E ∈ Γ, Eᵛ = □B := by simpa using h
  obtain ⟨C, D, rfl, rfl⟩ := visser_eq_box.mp hEB
  exact ⟨C, D, hE, rfl⟩

end Translation

/-! ### The semantics of the translation -/

namespace Modal.Model

variable {κ α : Type*} {M : Model κ α}

/-- - [Vis81, Theorem 5.4] -/
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

/-- - [Vis81, Theorem 5.4] -/
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

/-- - [Vis81, Theorem 5.4] -/
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
