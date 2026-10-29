module

public import Subintuitionistic.Propositional.FPL.Basic
public import Subintuitionistic.Propositional.Kripke
public import Subintuitionistic.Modal.Kripke
public import Mathlib.Data.Finset.Image

/-!
# The Gödel and Visser translations

The translations `Aᵍ` and `Aᵛ` of propositional formulas into modal formulas, and their
elementwise extension to finite sets of formulas.

## References

- [Vis81, 5.3]
-/

@[expose] public section

namespace Propositional

namespace Formula

open Modal

variable {α : Type*}

/-- - [Vis81, 5.3] -/
@[grind]
def gödel : Formula α → Modal.Formula α
  | .atom a  => □#a
  | .falsum  => □⊥
  | .and A B => A.gödel ⋏ B.gödel
  | .or A B  => A.gödel ⋎ B.gödel
  | .imp A B => □(A.gödel 🡒 B.gödel)

/-- - [Vis81, 5.3] -/
@[grind]
def visser : Formula α → Modal.Formula α
  | .atom a  => #a ⋏ □#a
  | .falsum  => ⊥
  | .and A B => A.visser ⋏ B.visser
  | .or A B  => A.visser ⋎ B.visser
  | .imp A B => □(A.visser 🡒 B.visser)

@[inherit_doc] postfix:max "ᵍ" => Formula.gödel
@[inherit_doc] postfix:max "ᵛ" => Formula.visser

@[simp, grind =] lemma visser_bot : (⊥ : Formula α)ᵛ = ⊥ := rfl

end Formula

namespace FormulaFinset

variable {α : Type*} [DecidableEq α] {Γ : FormulaFinset α} {B : Modal.Formula α}

def gödel (Γ : FormulaFinset α) : Modal.FormulaFinset α := Γ.image Formula.gödel

def visser (Γ : FormulaFinset α) : Modal.FormulaFinset α := Γ.image Formula.visser

@[inherit_doc] postfix:max "ᵍ" => FormulaFinset.gödel
@[inherit_doc] postfix:max "ᵛ" => FormulaFinset.visser

@[simp, grind =] lemma mem_gödel : B ∈ Γᵍ ↔ ∃ A ∈ Γ, Aᵍ = B := Finset.mem_image

@[simp, grind =] lemma mem_visser : B ∈ Γᵛ ↔ ∃ A ∈ Γ, Aᵛ = B := Finset.mem_image

@[simp] lemma gödel_empty : (∅ : FormulaFinset α)ᵍ = ∅ := Finset.image_empty _

@[simp] lemma visser_empty : (∅ : FormulaFinset α)ᵛ = ∅ := Finset.image_empty _

@[simp, grind =] lemma visser_insert {A : Formula α} : (insert A Γ)ᵛ = insert Aᵛ Γᵛ :=
  Finset.image_insert _ _ _

@[simp, grind =] lemma visser_union {Δ : FormulaFinset α} : (Γ ∪ Δ)ᵛ = Γᵛ ∪ Δᵛ :=
  Finset.image_union _ _

@[simp, grind =] lemma visser_singleton {A : Formula α} : ({A} : FormulaFinset α)ᵛ = {Aᵛ} :=
  Finset.image_singleton _ _

@[simp, grind =] lemma visser_image {β : Type*} (f : β → Formula α) (I : Finset β) :
    (I.image f)ᵛ = I.image fun x ↦ (f x)ᵛ := Finset.image_image

open Modal in
@[simp] lemma visser_imps (P : Finset (Formula α × Formula α)) :
    (logicFPL.imps P)ᵛ = P.image fun p ↦ □(p.1ᵛ 🡒 p.2ᵛ) := by
  simp [logicFPL.imps, Formula.visser]

end FormulaFinset

end Propositional

namespace Modal.Model.World

variable {κ α : Type*} {M : Model κ α} {x : M.World}

@[grind .]
lemma forces_gödel_of_terminal (hx : ∀ y, x ⊀ y) (A : Propositional.Formula α) : x ⊩ Aᵍ := by
  induction A <;> grind

end Modal.Model.World

end
