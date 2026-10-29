module

public import Subintuitionistic.Modal.Sequent
public import Mathlib.Order.Defs.Unbundled
public import Mathlib.Data.Fintype.Card

/-!
# Kripke semantics of `GL`

Kripke models, forcing and validity of sequents for modal formulas, and the frame classes
`IsFiniteGL` (finite, irreflexive, transitive) and the wider `IsGL` (transitive, conversely
well-founded).
-/

@[expose] public section

namespace Modal

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

/-- - [Seg71] -/
class IsFiniteGL (M : Model κ α) : Prop extends IsTrans _ M.Rel, Std.Irrefl M.Rel where
  [finite : Finite M.World]

attribute [instance] IsFiniteGL.finite

/-- - [Boo94] -/
class IsGL (M : Model κ α) : Prop extends IsTrans _ M.Rel where
  converseWellFounded : WellFounded (Function.swap M.Rel)

end Model

namespace Model.World

variable {κ α : Type*} {M : Model κ α} {x : M.World} {A B : Formula α}

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

@[grind]
def ForcesSequent (M : Model κ α) (x : M.World) (S : Sequent α) : Prop :=
  (∀ C ∈ S.ant, x ⊩ C) → ∃ D ∈ S.suc, x ⊩ D

scoped[Modal] notation:55 x:56 " ⊩[" M "] " S:56 => Model.World.ForcesSequent M x S
scoped[Modal] notation:55 x:56 " ⊩ " S:56 => Model.World.ForcesSequent _ x S

section

variable {Γ Γ' Γ₁ Γ₂ Δ Δ' Δ₁ Δ₂ : FormulaFinset α}

lemma forcesSequent_wk (h : x ⊩ (Γ ⟹ Δ)) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : x ⊩ (Γ' ⟹ Δ') := by
  grind

variable [DecidableEq α]

lemma forcesSequent_impL (h₁ : x ⊩ (Γ ⟹ insert A Δ)) (h₂ : x ⊩ (insert B Γ ⟹ Δ)) :
    x ⊩ (insert (A 🡒 B) Γ ⟹ Δ) := by
  intro hΓ
  have hΓ' : ∀ C ∈ Γ, x ⊩ C := fun C hC ↦ hΓ C (Finset.mem_insert_of_mem hC)
  have hAB : x ⊩ A 🡒 B := hΓ _ (Finset.mem_insert_self _ _)
  obtain ⟨D, hD, hxD⟩ := h₁ hΓ'
  rcases Finset.mem_insert.mp hD with rfl | hD
  · exact h₂ (by grind)
  · exact ⟨D, hD, hxD⟩

lemma forcesSequent_impR (h : x ⊩ (insert A Γ ⟹ insert B Δ)) : x ⊩ (Γ ⟹ insert (A 🡒 B) Δ) := by
  intro hΓ
  by_cases hA : x ⊩ A
  · obtain ⟨D, hD, hxD⟩ := h (by grind)
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact ⟨_, Finset.mem_insert_self _ _, fun _ ↦ hxD⟩
    · exact ⟨D, Finset.mem_insert_of_mem hD, hxD⟩
  · exact ⟨_, Finset.mem_insert_self _ _, fun h ↦ (hA h).elim⟩

lemma forcesSequent_cut (h₁ : x ⊩ (Γ₁ ⟹ insert A Δ₁)) (h₂ : x ⊩ (insert A Γ₂ ⟹ Δ₂)) :
    x ⊩ (Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂) := by
  grind

end

end Model.World

namespace Model

open World

variable {κ α : Type*} {M : Model κ α} {Γ : FormulaFinset α} {A : Formula α}

@[grind]
def ValidateSequent (M : Model κ α) (S : Sequent α) : Prop := ∀ x : M.World, x ⊩ S

scoped[Modal] infix:45 " ⊧ " => Model.ValidateSequent

lemma validateSequent_singleton_iff : M ⊧ (Γ ⟹ {A}) ↔ ∀ x : M.World, (∀ C ∈ Γ, x ⊩ C) → x ⊩ A :=
  forall_congr' fun _ ↦ imp_congr_right fun _ ↦ by simp

instance [M.IsFiniteGL] : M.IsGL where
  converseWellFounded := Finite.wellFounded_of_trans_of_irrefl _

end Model

end Modal

end
