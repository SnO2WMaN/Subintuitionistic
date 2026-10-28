module

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

variable {α : Type*}

/-- The Gödel translation: `pᵍ = □p`, `⊥ᵍ = □⊥`, `(A 🡒 B)ᵍ = □(Aᵍ 🡒 Bᵍ)`, commuting with `⋏`
and `⋎`.
- [Vis81, 5.3] -/
@[grind]
def gödel : Formula α → Modal.Formula α
  | .atom a  => .box (.atom a)
  | .falsum  => .box ⊥
  | .and A B => .and A.gödel B.gödel
  | .or A B  => .or A.gödel B.gödel
  | .imp A B => .box (.imp A.gödel B.gödel)

/-- The Visser translation: `pᵛ = p ⋏ □p`, `⊥ᵛ = ⊥`, `(A 🡒 B)ᵛ = □(Aᵛ 🡒 Bᵛ)`, commuting with `⋏`
and `⋎`.
- [Vis81, 5.3] -/
@[grind]
def visser : Formula α → Modal.Formula α
  | .atom a  => .and (.atom a) (.box (.atom a))
  | .falsum  => ⊥
  | .and A B => .and A.visser B.visser
  | .or A B  => .or A.visser B.visser
  | .imp A B => .box (.imp A.visser B.visser)

@[inherit_doc] postfix:max "ᵍ" => Formula.gödel
@[inherit_doc] postfix:max "ᵛ" => Formula.visser

end Formula

namespace FormulaFinset

variable {α : Type*} [DecidableEq α] {Γ : FormulaFinset α} {B : Modal.Formula α}

/-- The Gödel translation of every formula of `Γ`. -/
def gödel (Γ : FormulaFinset α) : Modal.FormulaFinset α := Γ.image Formula.gödel

/-- The Visser translation of every formula of `Γ`. -/
def visser (Γ : FormulaFinset α) : Modal.FormulaFinset α := Γ.image Formula.visser

@[inherit_doc] postfix:max "ᵍ" => FormulaFinset.gödel
@[inherit_doc] postfix:max "ᵛ" => FormulaFinset.visser

@[simp, grind =] lemma mem_gödel : B ∈ Γᵍ ↔ ∃ A ∈ Γ, Aᵍ = B := Finset.mem_image

@[simp, grind =] lemma mem_visser : B ∈ Γᵛ ↔ ∃ A ∈ Γ, Aᵛ = B := Finset.mem_image

@[simp] lemma gödel_empty : (∅ : FormulaFinset α)ᵍ = ∅ := Finset.image_empty _

@[simp] lemma visser_empty : (∅ : FormulaFinset α)ᵛ = ∅ := Finset.image_empty _

end FormulaFinset

end Propositional

namespace Modal.Model.World

variable {κ α : Type*} {M : Model κ α} {x : M.World}

/-- The Gödel translation is forced at every terminal point. -/
@[grind .]
lemma forces_gödel_of_terminal (hx : ∀ y, x ⊀ y) (A : Propositional.Formula α) : x ⊩ Aᵍ := by
  induction A <;> grind

end Modal.Model.World

end
