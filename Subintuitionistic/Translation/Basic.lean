module

public import Subintuitionistic.Modal.Kripke.Basic
public import Subintuitionistic.Propositional.Kripke.Basic

/-!
# The Gödel and Visser translations

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

variable {A : Formula α} {a : α} {B C : Modal.Formula α}

@[simp, grind .] lemma visser_ne_atom : Aᵛ ≠ .atom a := by
  cases A <;> simp [visser, Modal.Formula.and, Modal.Formula.or, Modal.Formula.neg]

@[simp, grind =] lemma visser_eq_bot : Aᵛ = ⊥ ↔ A = ⊥ := by
  cases A <;> simp [visser, Modal.Formula.and, Modal.Formula.or, Modal.Formula.neg]

lemma visser_eq_box : Aᵛ = □B ↔ ∃ C D, A = .imp C D ∧ B = Cᵛ 🡒 Dᵛ := by
  cases A <;> simp [visser, Modal.Formula.and, Modal.Formula.or, Modal.Formula.neg, eq_comm]

lemma visser_eq_imp :
    Aᵛ = B 🡒 C ↔ (∃ a, A = .atom a ∧ B = #a 🡒 ∼□#a ∧ C = ⊥) ∨
      (∃ D E, A = .and D E ∧ B = Dᵛ 🡒 ∼Eᵛ ∧ C = ⊥) ∨ (∃ D E, A = .or D E ∧ B = ∼Dᵛ ∧ C = Eᵛ) := by
  cases A <;> simp [visser, Modal.Formula.and, Modal.Formula.or, Modal.Formula.neg, eq_comm]

lemma visser_injective : Function.Injective (visser (α := α)) := by
  intro A B hAB
  induction A generalizing B with
  | atom a | falsum | and A₁ A₂ ih₁ ih₂ | or A₁ A₂ ih₁ ih₂ | imp A₁ A₂ ih₁ ih₂ =>
    cases B <;>
      simp [visser, Modal.Formula.and, Modal.Formula.or, Modal.Formula.neg] at hAB ⊢ <;> grind

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
    (imps P)ᵛ = P.image fun p ↦ □(p.1ᵛ 🡒 p.2ᵛ) := by
  simp [imps, Formula.visser]

@[grind =] lemma visser_erase_bot : (Γ.erase ⊥)ᵛ = Γᵛ.erase ⊥ := by
  ext x
  grind

open Modal in
@[grind →] lemma exists_imp_of_box_mem_visser (h : □B ∈ Γᵛ) :
    ∃ C D, .imp C D ∈ Γ ∧ B = Cᵛ 🡒 Dᵛ := by
  obtain ⟨E, hE, hEB⟩ : ∃ E ∈ Γ, Eᵛ = □B := by simpa using h
  obtain ⟨C, D, rfl, rfl⟩ := Formula.visser_eq_box.mp hEB
  exact ⟨C, D, hE, rfl⟩

end FormulaFinset

end Propositional

namespace Modal.Model.World

variable {κ α : Type*} {M : Model κ α} {x : M.World}

@[grind .]
lemma forces_gödel_of_terminal (hx : ∀ y, x ⊀ y) (A : Propositional.Formula α) : x ⊩ Aᵍ := by
  induction A <;> grind

end Modal.Model.World

end
