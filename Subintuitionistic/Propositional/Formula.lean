module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Union

/-!
# Propositional formulas

Formulas built from variables and `⊥` with `⋏`, `⋎` and `🡒`, and their subformulas. The
connectives share their notation with modal formulas (`Modal.Formula`); the notation is scoped to
the namespace `Propositional`, and the expected type tells the two apart.
-/

@[expose] public section

namespace Propositional

inductive Formula (α : Type*) where
  | atom   : α → Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq

abbrev FormulaSet (α : Type*) := Set (Formula α)

abbrev Logic (α : Type*) := Set (Formula α)

abbrev FormulaFinset (α : Type*) := Finset (Formula α)

namespace Formula

variable {α : Type*}

instance : Bot (Formula α) := ⟨falsum⟩

scoped[Propositional] prefix:max "#" => Formula.atom
scoped[Propositional] infixr:60 " 🡒 " => Formula.imp
scoped[Propositional] infixr:69 " ⋏ " => Formula.and
scoped[Propositional] infixr:68 " ⋎ " => Formula.or

@[simp] lemma falsum_eq : (falsum : Formula α) = ⊥ := rfl

@[grind =] lemma bot_eq_falsum : (⊥ : Formula α) = falsum := rfl

/-- Recursion on formulas, with the cases written in notation. -/
@[elab_as_elim, induction_eliminator]
def rec' {motive : Formula α → Sort*} (atom : ∀ a, motive (#a)) (falsum : motive ⊥)
    (and : ∀ A B, motive A → motive B → motive (A ⋏ B))
    (or : ∀ A B, motive A → motive B → motive (A ⋎ B))
    (imp : ∀ A B, motive A → motive B → motive (A 🡒 B)) : ∀ A, motive A
  | .atom a  => atom a
  | .falsum  => falsum
  | .and A B => and A B (rec' atom falsum and or imp A) (rec' atom falsum and or imp B)
  | .or A B  => or A B (rec' atom falsum and or imp A) (rec' atom falsum and or imp B)
  | .imp A B => imp A B (rec' atom falsum and or imp A) (rec' atom falsum and or imp B)

/-- Case analysis on formulas, with the cases written in notation. -/
@[elab_as_elim, cases_eliminator]
def cases' {motive : Formula α → Sort*} (atom : ∀ a, motive (#a)) (falsum : motive ⊥)
    (and : ∀ A B, motive (A ⋏ B)) (or : ∀ A B, motive (A ⋎ B)) (imp : ∀ A B, motive (A 🡒 B)) :
    ∀ A, motive A
  | .atom a  => atom a
  | .falsum  => falsum
  | .and A B => and A B
  | .or A B  => or A B
  | .imp A B => imp A B

/-! ### Subformulas -/

variable [DecidableEq α] {A B : Formula α}

/-- The formula itself is included. -/
def subfmls : Formula α → FormulaFinset α
  | .atom a  => {.atom a}
  | .falsum  => {⊥}
  | .and A B => insert (A ⋏ B) (A.subfmls ∪ B.subfmls)
  | .or A B  => insert (A ⋎ B) (A.subfmls ∪ B.subfmls)
  | .imp A B => insert (A 🡒 B) (A.subfmls ∪ B.subfmls)

@[simp, grind .] lemma mem_subfmls_self (A : Formula α) : A ∈ A.subfmls := by
  cases A <;> simp [subfmls]

@[grind →] lemma subfmls_subset_of_mem (h : B ∈ A.subfmls) : B.subfmls ⊆ A.subfmls := by
  induction A with
  | atom a | falsum => simp_all [subfmls]
  | and A₁ A₂ ih₁ ih₂ | or A₁ A₂ ih₁ ih₂ | imp A₁ A₂ ih₁ ih₂ =>
    grind [subfmls]

end Formula

namespace FormulaFinset

variable {α : Type*}

structure SubformulaClosed (Γ : FormulaFinset α) : Prop where
  and : ∀ {A B}, A ⋏ B ∈ Γ → A ∈ Γ ∧ B ∈ Γ
  or  : ∀ {A B}, A ⋎ B ∈ Γ → A ∈ Γ ∧ B ∈ Γ
  imp : ∀ {A B}, A 🡒 B ∈ Γ → A ∈ Γ ∧ B ∈ Γ

variable [DecidableEq α] {Γ : FormulaFinset α}

def subfmls (Γ : FormulaFinset α) : FormulaFinset α := Γ.biUnion Formula.subfmls

@[grind .] lemma subset_subfmls : Γ ⊆ Γ.subfmls :=
  fun A hA ↦ Finset.mem_biUnion.mpr ⟨A, hA, Formula.mem_subfmls_self A⟩

lemma subformulaClosed_subfmls : Γ.subfmls.SubformulaClosed := by
  have key : ∀ {B C}, B ∈ Γ.subfmls → C ∈ B.subfmls → C ∈ Γ.subfmls := by
    intro B C hB hC
    obtain ⟨A, hA, hBA⟩ := Finset.mem_biUnion.mp hB
    exact Finset.mem_biUnion.mpr ⟨A, hA, Formula.subfmls_subset_of_mem hBA hC⟩
  constructor <;> exact fun h ↦ ⟨key h (by simp [Formula.subfmls]),
    key h (by simp [Formula.subfmls])⟩

end FormulaFinset

end Propositional

end
