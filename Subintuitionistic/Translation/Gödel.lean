module

public import Subintuitionistic.Translation.Basic
public import Mathlib.Basic.Finite.Sum

/-!
# Semantics of the Gödel translation

The FPL model `M.removeTerminals` on the non-terminal points of a GL model `M`, the GL model
`K.addTerminals` of an FPL model `K`, the forcing of `Aᵍ` in them, and the equivalence of validity
of `Γ ⟹ A` in FPL models with validity of `Γᵍ ⟹ Aᵍ` in GL models.

## References

- [Vis81, Theorem 5.4]
-/

@[expose] public section

open Propositional.Formula

namespace Modal.Model

variable {κ α : Type*} {M : Model κ α}

/-- The non-terminal points of `M`. -/
def NonTerminal (M : Model κ α) : Type _ := { x : M.World // ∃ y, x ≺ y }

/-- The FPL model on the non-terminal points of `M` whose truth set of `p` is the truth set of
`□p` in `M`.
- [Vis81, Theorem 5.4] -/
def removeTerminals (M : Model κ α) [IsTrans _ M.Rel] : Propositional.Model M.NonTerminal α where
  Rel' x y := x.1 ≺ y.1
  Val' x a := ∀ y, x.1 ≺ y → M y a
  hereditary' Rxy _ h z Ryz := h z (_root_.trans Rxy Ryz)

variable [M.IsFiniteGL]

@[simp, grind _=_] lemma removeTerminals_rel {x y : M.NonTerminal} :
    M.removeTerminals.Rel x y ↔ x.1 ≺ y.1 := Iff.rfl

@[simp, grind =] lemma removeTerminals_val {x : M.NonTerminal} {a : α} :
    M.removeTerminals x a ↔ x.1 ⊩ □#a := Iff.rfl

instance : M.removeTerminals.IsFPL where
  trans _ _ _ := IsTrans.trans (r := M.Rel) _ _ _
  irrefl x := Std.Irrefl.irrefl (r := M.Rel) x.1
  finite := inferInstanceAs (Finite { x : M.World // ∃ y, x ≺ y })

open Propositional in
lemma removeTerminals_forces_iff {x : M.removeTerminals.World} {A : Propositional.Formula α} :
    x ⊩[M.removeTerminals] A ↔ x.1 ⊩ Aᵍ := by
  induction A generalizing x with
  | atom a => grind
  | falsum => grind [x.2]
  | and A B ihA ihB | or A B ihA ihB => grind
  | imp A B ihA ihB =>
    have h₁ (z : M.World) (hz : ∃ w, M.Rel z w) := ihA (x := ⟨z, hz⟩)
    have h₂ (z : M.World) (hz : ∃ w, M.Rel z w) := ihB (x := ⟨z, hz⟩)
    grind

end Modal.Model

namespace Propositional.Model

variable {κ α : Type*} {K : Model κ α}

/-- The GL model on `K.World ⊕ K.World` in which each point `w` of `K` (`Sum.inl w`) sees a new
terminal point `w'` (`Sum.inr w`) with the valuation of `w`, and `w'` is seen by `w` and by every
point that sees `w`.
- [Vis81, Theorem 5.4] -/
def addTerminals (K : Model κ α) : Modal.Model (K.World ⊕ K.World) α where
  Rel'
    | .inl u, .inl w => u ≺ w
    | .inl u, .inr w => u = w ∨ u ≺ w
    | .inr _, _      => False
  Val'
    | .inl w, a => K w a
    | .inr w, a => K w a

@[simp, grind _=_] lemma addTerminals_rel_inl_inl {u w : K.World} :
    K.addTerminals.Rel (.inl u) (.inl w) ↔ u ≺ w := Iff.rfl

@[simp, grind =] lemma addTerminals_rel_inl_inr {u w : K.World} :
    K.addTerminals.Rel (.inl u) (.inr w) ↔ u = w ∨ u ≺ w := Iff.rfl

lemma addTerminals_rel_inl_inr_self (w : K.World) :
    K.addTerminals.Rel (.inl w) (.inr w) := Or.inl rfl

@[simp, grind .] lemma not_addTerminals_rel_inr {w : K.World} {y : K.addTerminals.World} :
    ¬K.addTerminals.Rel (.inr w) y := id

@[simp, grind =] lemma addTerminals_val_inl {w : K.World} {a : α} :
    K.addTerminals (.inl w) a ↔ K w a := Iff.rfl

@[simp, grind =] lemma addTerminals_val_inr {w : K.World} {a : α} :
    K.addTerminals (.inr w) a ↔ K w a := Iff.rfl

instance [K.IsFPL] : K.addTerminals.IsFiniteGL where
  trans := by
    have h₁ (u v w : K.World) := _root_.trans (r := K.Rel) (a := u) (b := v) (c := w)
    rintro (u | u) (v | v) (w | w) <;> grind
  irrefl := by
    have h₁ := Std.Irrefl.irrefl (r := K.Rel)
    rintro (u | u) <;> grind
  finite := inferInstanceAs (Finite (K.World ⊕ K.World))

open Modal in
lemma addTerminals_forces_gödel_iff [K.IsFPL] {w : K.World} {A : Formula α} :
    Sum.inl w ⊩[K.addTerminals] Aᵍ ↔ w ⊩ A := by
  induction A generalizing w with
  | atom a => grind [addTerminals_rel_inl_inr_self w]
  | falsum => grind [addTerminals_rel_inl_inr_self w]
  | and A B ihA ihB | or A B ihA ihB => grind
  | imp A B ihA ihB => grind [addTerminals_rel_inl_inr_self w]

end Propositional.Model

namespace Translation

open Propositional Modal

universe u

variable {α : Type u} [DecidableEq α] {Γ : Propositional.FormulaFinset α}
  {A : Propositional.Formula α}

/-- `Γ ⟹ {A}` is valid in every FPL model if and only if `Γᵍ ⟹ {Aᵍ}` is valid in every GL model.
- [Vis81, Theorem 5.4] -/
theorem valid_iff_gödel :
    (∀ {κ : Type u} (K : Propositional.Model κ α), [K.IsFPL] → K ⊧ Γ ⟹ {A}) ↔
    ∀ {κ : Type u} (M : Modal.Model κ α), [M.IsFiniteGL] → M ⊧ Γᵍ ⟹ {Aᵍ} := by
  constructor
  · intro h κ M _
    apply Modal.Model.validateSequent_singleton_iff.mpr
    intro x hΓ
    by_cases hx : ∃ y, M.Rel x y
    · have h₁ := Propositional.Model.validateSequent_singleton_iff.mp (h M.removeTerminals) ⟨x, hx⟩
      grind [Modal.Model.removeTerminals_forces_iff]
    · grind
  · intro h κ K _
    apply Propositional.Model.validateSequent_singleton_iff.mpr
    intro w hΓ
    have h₁ := Modal.Model.validateSequent_singleton_iff.mp (h K.addTerminals) (.inl w)
    grind [Propositional.Model.addTerminals_forces_gödel_iff]

end Translation

end
