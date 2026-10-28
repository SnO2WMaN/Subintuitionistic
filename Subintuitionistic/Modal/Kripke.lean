module

public import Subintuitionistic.Modal.Sequent
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Data.Fintype.Card

/-!
# Kripke semantics of `GL`

Kripke models and forcing for modal formulas, and the class of GL models: finite irreflexive
transitive frames with arbitrary valuations.
-/

@[expose] public section

namespace Modal

/-- A Kripke model. -/
structure Model (κ α : Type*) where
  Rel' : κ → κ → Prop
  Val' : κ → α → Prop

namespace Model

variable {κ α : Type*}

abbrev World (_ : Model κ α) := κ

abbrev Rel {M : Model κ α} : M.World → M.World → Prop := M.Rel'
scoped[Modal] infix:60 " ≺ " => Model.Rel

abbrev NotRel {M : Model κ α} (x y : M.World) : Prop := ¬x ≺ y
scoped[Modal] infix:60 " ⊀ " => Model.NotRel

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

instance : CoeFun (Model κ α) (fun M ↦ M.World → α → Prop) := ⟨fun M ↦ M.Val⟩

/-- A GL model: the frame is finite, irreflexive and transitive.

- [Seg71] -/
class IsFiniteGL (M : Model κ α) : Prop extends IsTrans _ M.Rel, Std.Irrefl M.Rel where
  [finite : Finite M.World]

attribute [instance] IsFiniteGL.finite

end Model

namespace Model.World

variable {κ α : Type*} {M : Model κ α} {x : M.World} {A B : Formula α}

/-- The forcing relation. -/
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
  | .atom a  => M x a
  | .falsum  => False
  | .imp A B => Forces M x A → Forces M x B
  | .box A   => ∀ y, x ≺ y → Forces M y A

scoped[Modal] notation:55 x:56 " ⊩[" M "] " A:56 => Model.World.Forces M x A
scoped[Modal] notation:55 x:56 " ⊮[" M "] " A:56 => ¬Model.World.Forces M x A
scoped[Modal] notation:55 x:56 " ⊩ " A:56 => Model.World.Forces _ x A
scoped[Modal] notation:55 x:56 " ⊮ " A:56 => ¬Model.World.Forces _ x A

@[simp, grind =] lemma forces_atom {a : α} : x ⊩ #a ↔ M x a := Iff.rfl
@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := id
@[simp, grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ (x ⊩ A → x ⊩ B) := Iff.rfl
@[simp, grind =] lemma forces_box : x ⊩ □A ↔ ∀ y, x ≺ y → y ⊩ A := Iff.rfl
@[simp, grind =] lemma forces_neg : x ⊩ ∼A ↔ x ⊮ A := Iff.rfl
@[simp, grind .] lemma forces_top : x ⊩ ⊤ := id

@[simp, grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := by
  grind [Formula.and, Formula.neg]

@[simp, grind =] lemma forces_or : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := by
  grind [Formula.or, Formula.neg]

/-- The sequent `S` holds at `x`: if `x` forces all of its antecedent, it forces some formula of
its succedent. -/
@[grind]
def ForcesSequent (M : Model κ α) (x : M.World) (S : Sequent α) : Prop :=
  (∀ C ∈ S.ant, x ⊩ C) → ∃ D ∈ S.suc, x ⊩ D

scoped[Modal] notation:55 x:56 " ⊩[" M "] " S:56 => Model.World.ForcesSequent M x S
scoped[Modal] notation:55 x:56 " ⊩ " S:56 => Model.World.ForcesSequent _ x S

end Model.World

namespace Model

open World

variable {κ α : Type*} {M : Model κ α} {Γ : FormulaFinset α} {A : Formula α}

/-- The sequent `S` holds at every point of `M`. -/
@[grind]
def ValidateSequent (M : Model κ α) (S : Sequent α) : Prop := ∀ x : M.World, x ⊩ S

scoped[Modal] infix:45 " ⊧ " => Model.ValidateSequent

lemma validateSequent_singleton_iff : M ⊧ (Γ ⟹ {A}) ↔ ∀ x : M.World, (∀ C ∈ Γ, x ⊩ C) → x ⊩ A :=
  forall_congr' fun _ ↦ imp_congr_right fun _ ↦ by simp

/-- The converse of the accessibility relation of a GL model is well-founded. -/
lemma wellFounded_swap_rel [M.IsFiniteGL] : WellFounded (Function.swap M.Rel) :=
  Finite.wellFounded_of_trans_of_irrefl _

end Model

end Modal

end
