module

public import Subintuitionistic.Modal.GL.Kripke
public import Subintuitionistic.Propositional.FPL.Kripke
public import Subintuitionistic.Translation.Basic
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Tactic.TFAE

/-!
# Embeddings of `𝐅𝐏𝐋` into `𝐆𝐋`

## References

- [Vis81, Theorem 5.4]
-/

@[expose] public section

universe u

open Propositional.Formula

/-! ### The Gödel translation -/

namespace Modal.Model

variable {κ α : Type*} {M : Model κ α}

def NonTerminal (M : Model κ α) : Type _ := { x : M.World // ∃ y, x ≺ y }

/-- - [Vis81, Theorem 5.4] -/
def removeTerminals (M : Model κ α) [IsTrans _ M.Rel] : Propositional.Model M.NonTerminal α where
  Rel' x y := x.1 ≺ y.1
  Val' x a := ∀ y, x.1 ≺ y → M y a
  hereditary' Rxy _ h z Ryz := h z (_root_.trans Rxy Ryz)

variable [M.IsFiniteGL] {x y : M.removeTerminals.World} {a : α}

@[simp, grind _=_]
lemma removeTerminals_rel : M.removeTerminals.Rel x y ↔ x.1 ≺ y.1 := Iff.rfl

@[simp, grind =]
lemma removeTerminals_val : M.removeTerminals x a ↔ x.1 ⊩ □#a := Iff.rfl

instance : M.removeTerminals.IsFiniteFPL where
  trans _ _ _ := IsTrans.trans (r := M.Rel) _ _ _
  irrefl x := Std.Irrefl.irrefl (r := M.Rel) x.1
  finite := inferInstanceAs (Finite { x : M.World // ∃ y, x ≺ y })

open Propositional in
lemma removeTerminals_forces_iff {A : Propositional.Formula α} : x ⊩ A ↔ x.1 ⊩ Aᵍ := by
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

variable {κ α : Type*} {K : Model κ α} {u w : K.World}

/-- - [Vis81, Theorem 5.4] -/
def addTerminals (K : Model κ α) : Modal.Model (K.World ⊕ K.World) α where
  Rel'
    | .inl u, .inl w => u ≺ w
    | .inl u, .inr w => u = w ∨ u ≺ w
    | .inr _, _      => False
  Val'
    | .inl w, a => K w a
    | .inr w, a => K w a

@[simp, grind _=_] lemma addTerminals_rel_inl_inl :
    K.addTerminals.Rel (.inl u) (.inl w) ↔ u ≺ w := Iff.rfl

@[simp, grind =] lemma addTerminals_rel_inl_inr :
    K.addTerminals.Rel (.inl u) (.inr w) ↔ u = w ∨ u ≺ w := Iff.rfl

lemma addTerminals_rel_inl_inr_self (w : K.World) :
    K.addTerminals.Rel (.inl w) (.inr w) := Or.inl rfl

@[simp, grind .] lemma not_addTerminals_rel_inr {y : K.addTerminals.World} :
    ¬K.addTerminals.Rel (.inr w) y := id

@[simp, grind =] lemma addTerminals_val_inl {a : α} :
    K.addTerminals (.inl w) a ↔ K w a := Iff.rfl

@[simp, grind =] lemma addTerminals_val_inr {a : α} :
    K.addTerminals (.inr w) a ↔ K w a := Iff.rfl

instance [K.IsFiniteFPL] : K.addTerminals.IsFiniteGL where
  trans := by
    have h₁ (u v w : K.World) := _root_.trans (r := K.Rel) (a := u) (b := v) (c := w)
    rintro (u | u) (v | v) (w | w) <;> grind
  irrefl := by
    have h₁ := Std.Irrefl.irrefl (r := K.Rel)
    rintro (u | u) <;> grind
  finite := inferInstanceAs (Finite (K.World ⊕ K.World))

open Modal in
lemma addTerminals_forces_gödel_iff [K.IsFiniteFPL] {w : K.World} {A : Formula α} :
    Sum.inl w ⊩[K.addTerminals] Aᵍ ↔ w ⊩ A := by
  induction A generalizing w with
  | atom a => grind [addTerminals_rel_inl_inr_self w]
  | falsum => grind [addTerminals_rel_inl_inr_self w]
  | and A B ihA ihB | or A B ihA ihB => grind
  | imp A B ihA ihB => grind [addTerminals_rel_inl_inr_self w]

end Propositional.Model

/-! ### The Visser translation -/

namespace Modal.Model

variable {κ α : Type*} {M : Model κ α}

/-- - [Vis81, Theorem 5.4] -/
def boxdotVal (M : Model κ α) [IsTrans _ M.Rel] : Propositional.Model κ α where
  Rel' := M.Rel
  Val' x a := M x a ∧ ∀ y, M.Rel x y → M y a
  hereditary' Rxy _ := fun ⟨_, h⟩ ↦ ⟨h _ Rxy, fun z Ryz ↦ h z (_root_.trans Rxy Ryz)⟩

section

variable [IsTrans _ M.Rel]

@[simp, grind _=_] lemma boxdotVal_rel {x y : M.World} : M.boxdotVal.Rel x y ↔ M.Rel x y := Iff.rfl

@[simp, grind =] lemma boxdotVal_val {x : M.World} {a : α} :
    M.boxdotVal x a ↔ M x a ∧ ∀ y, x ≺ y → M y a := Iff.rfl

open Propositional in
lemma boxdotVal_forces_iff {x : M.World} {A : Propositional.Formula α} :
    x ⊩[M.boxdotVal] A ↔ x ⊩ Aᵛ := by
  induction A generalizing x with
  | falsum | atom a | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB => grind

open Propositional in
lemma boxdotVal_forcesSequent_iff [DecidableEq α] {x : M.World}
    {Γ Δ : Propositional.FormulaFinset α} :
    x ⊩[M.boxdotVal] (Γ ⟹ Δ) ↔ x ⊩ (Γᵛ ⟹ Δᵛ) := by
  simp [Propositional.Model.World.ForcesSequent, World.ForcesSequent, boxdotVal_forces_iff]

end

instance [M.IsFiniteGL] : M.boxdotVal.IsFiniteFPL where
  trans := IsTrans.trans (r := M.Rel)
  irrefl := Std.Irrefl.irrefl (r := M.Rel)
  finite := inferInstanceAs (Finite M.World)

instance [M.IsGL] : M.boxdotVal.IsFPL where
  trans := IsTrans.trans (r := M.Rel)
  converseWellFounded := IsGL.converseWellFounded (M := M)

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

instance [K.IsFiniteFPL] : K.toModal.IsFiniteGL where
  trans := IsTrans.trans (r := K.Rel)
  irrefl := Std.Irrefl.irrefl (r := K.Rel)
  finite := inferInstanceAs (Finite K.World)

instance [K.IsFPL] : K.toModal.IsGL where
  trans := IsTrans.trans (r := K.Rel)
  converseWellFounded := IsFPL.converseWellFounded (M := K)

open Modal in
lemma toModal_forces_visser_iff {x : K.World} {A : Formula α} :
    x ⊩[K.toModal] Aᵛ ↔ x ⊩ A := by
  induction A generalizing x with
  | atom a => grind
  | falsum | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB => grind

open Modal in
lemma toModal_forcesSequent_visser_iff [DecidableEq α] {x : K.World} {Γ Δ : FormulaFinset α} :
    x ⊩[K.toModal] (Γᵛ ⟹ Δᵛ) ↔ x ⊩ (Γ ⟹ Δ) := by
  simp [Modal.Model.World.ForcesSequent, World.ForcesSequent, toModal_forces_visser_iff]

end Propositional.Model

namespace Propositional

open Modal

variable {α : Type u} [DecidableEq α] {Γ Δ : FormulaFinset α} {A : Formula α}

namespace logicFPL.Derivable

/-- - [Vis81, Theorem 5.4] -/
theorem iff_gödel : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ {A} ↔ ⊢ᴳ[𝐆𝐋] Γᵍ ⟹ {Aᵍ} := by
  apply iff_valid.trans
  apply Iff.trans ?_ logicGL.Derivable.iff_valid.symm
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

/-- - [Vis81, Theorem 5.4] -/
theorem iff_visser : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ ↔ ⊢ᴳ[𝐆𝐋] Γᵛ ⟹ Δᵛ := by
  apply iff_valid.trans
  apply Iff.trans ?_ logicGL.Derivable.iff_valid.symm
  exact ⟨fun h _ M _ x ↦ Modal.Model.boxdotVal_forcesSequent_iff.mp (h M.boxdotVal x),
    fun h _ K _ x ↦ Propositional.Model.toModal_forcesSequent_visser_iff.mp (h K.toModal x)⟩

end logicFPL.Derivable

/-- - [Vis81, Theorem 5.4] -/
theorem mem_logicFPL_TFAE : [A ∈ 𝐅𝐏𝐋, Aᵍ ∈ 𝐆𝐋, Aᵛ ∈ 𝐆𝐋].TFAE := by
  tfae_have 1 ↔ 2 := by
    simpa [logicFPL, logicGL] using logicFPL.Derivable.iff_gödel (Γ := ∅) (A := A)
  tfae_have 1 ↔ 3 := by
    simpa [logicFPL, logicGL] using logicFPL.Derivable.iff_visser (Γ := ∅) (Δ := {A})
  tfae_finish

end Propositional

end
