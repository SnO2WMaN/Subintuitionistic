module

public import Subintuitionistic.Propositional.Sequent
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Data.Fintype.Card

/-!
# Kripke semantics of `FPL`

Kripke models with an upward closed valuation; an `FPL` model has a finite, irreflexive and
transitive frame. In the forcing relation, an implication `A 🡒 B` holds at `x` when every *proper*
successor of `x` forcing `A` forces `B`; `x` itself is not inspected, so modus ponens fails.
-/

@[expose] public section

namespace Propositional

/-- - [Vis81, 1.4] -/
structure Model (κ α : Type*) where
  Rel' : κ → κ → Prop
  Val' : κ → α → Prop
  hereditary' : ∀ {x y}, Rel' x y → ∀ {a}, Val' x a → Val' y a

namespace Model

variable {κ α : Type*} {M : Model κ α}

abbrev World (_ : Model κ α) := κ

abbrev Rel {M : Model κ α} : M.World → M.World → Prop := M.Rel'
scoped[Propositional] infix:60 " ≺ " => Model.Rel

abbrev NotRel {M : Model κ α} (x y : M.World) : Prop := ¬x ≺ y
scoped[Propositional] infix:60 " ⊀ " => Model.NotRel

abbrev Val {M : Model κ α} : M.World → α → Prop := M.Val'

instance : CoeFun (Model κ α) (fun M ↦ M.World → α → Prop) := ⟨fun M ↦ M.Val⟩

@[grind →] lemma hereditary {x y : M.World} (Rxy : x ≺ y) {a : α} : M x a → M y a :=
  M.hereditary' Rxy

/-- - [Vis81, 1.4]
- [IKK01, Section 3] -/
class IsFPL (M : Model κ α) : Prop extends IsTrans _ M.Rel, Std.Irrefl M.Rel where
  [finite : Finite M.World]

attribute [instance] IsFPL.finite

end Model

namespace Model.World

variable {κ α : Type*} {M : Model κ α} {x y : M.World} {A B : Formula α}

/-- - [Vis81, 1.4] -/
def Forces (M : Model κ α) (x : M.World) : Formula α → Prop
  | .atom a  => M x a
  | .falsum  => False
  | .and A B => Forces M x A ∧ Forces M x B
  | .or A B  => Forces M x A ∨ Forces M x B
  | .imp A B => ∀ y, x ≺ y → Forces M y A → Forces M y B

scoped[Propositional] notation:55 x:56 " ⊩[" M "] " A:56 => Model.World.Forces M x A
scoped[Propositional] notation:55 x:56 " ⊮[" M "] " A:56 => ¬Model.World.Forces M x A
scoped[Propositional] notation:55 x:56 " ⊩ " A:56 => Model.World.Forces _ x A
scoped[Propositional] notation:55 x:56 " ⊮ " A:56 => ¬Model.World.Forces _ x A

@[simp, grind =] lemma forces_atom {a : α} : x ⊩ #a ↔ M x a := Iff.rfl
@[simp, grind .] lemma not_forces_bot : x ⊮ ⊥ := id
@[simp, grind =] lemma forces_and : x ⊩ A ⋏ B ↔ x ⊩ A ∧ x ⊩ B := Iff.rfl
@[simp, grind =] lemma forces_or : x ⊩ A ⋎ B ↔ x ⊩ A ∨ x ⊩ B := Iff.rfl
@[grind =] lemma forces_imp : x ⊩ A 🡒 B ↔ ∀ y, x ≺ y → y ⊩ A → y ⊩ B := Iff.rfl

/-- Persistence.
- [Vis81, 1.4.2] -/
@[grind →] lemma forces_of_rel [IsTrans _ M.Rel] (Rxy : x ≺ y) (h : x ⊩ A) : y ⊩ A := by
  induction A generalizing x y with
  | atom a => exact M.hereditary Rxy h
  | falsum => exact h
  | and A B ihA ihB => exact ⟨ihA Rxy h.1, ihB Rxy h.2⟩
  | or A B ihA ihB => exact h.imp (ihA Rxy) (ihB Rxy)
  | imp A B _ _ => exact fun z Ryz ↦ h z (_root_.trans Rxy Ryz)

/-- - [IKK01, Section 3] -/
def ForcesSequent (M : Model κ α) (x : M.World) (S : Sequent α) : Prop :=
  (∀ C ∈ S.ant, x ⊩ C) → ∃ D ∈ S.suc, x ⊩ D

scoped[Propositional] notation:55 x:56 " ⊩[" M "] " S:56 => Model.World.ForcesSequent M x S
scoped[Propositional] notation:55 x:56 " ⊩ " S:56 => Model.World.ForcesSequent _ x S

end Model.World

namespace Model

open World

variable {κ α : Type*} {M : Model κ α} {Γ : FormulaFinset α} {A : Formula α}

/-- - [IKK01, Section 3] -/
def ValidateSequent (M : Model κ α) (S : Sequent α) : Prop := ∀ x : M.World, x ⊩ S

scoped[Propositional] infix:45 " ⊧ " => Model.ValidateSequent

@[grind =] lemma validateSequent_singleton_iff :
    M ⊧ (Γ ⟹ {A}) ↔ ∀ x : M.World, (∀ C ∈ Γ, x ⊩ C) → x ⊩ A :=
  forall_congr' fun _ ↦ imp_congr_right fun _ ↦ by simp

end Model

end Propositional

end
