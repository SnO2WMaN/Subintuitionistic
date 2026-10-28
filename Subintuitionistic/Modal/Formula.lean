module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Union

/-!
# Modal formulas

Formulas built from variables and `⊥` with `🡒` and `□`; `∼`, `⋏`, `⋎` and `⊤` are abbreviations.
The connectives share their notation with propositional formulas (`Propositional.Formula`); the
notation is scoped to the namespace `Modal`, and the expected type tells the two apart.
-/

@[expose] public section

namespace Modal

/-- Modal formulas over the atoms `α`. -/
inductive Formula (α : Type*) where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

abbrev FormulaSet (α : Type*) := Set (Formula α)

abbrev FormulaFinset (α : Type*) := Finset (Formula α)

namespace Formula

variable {α : Type*}

instance : Bot (Formula α) := ⟨falsum⟩

scoped[Modal] prefix:max "#" => Formula.atom
scoped[Modal] infixr:60 " 🡒 " => Formula.imp
scoped[Modal] prefix:76 "□" => Formula.box

@[simp] lemma falsum_eq : (falsum : Formula α) = ⊥ := rfl

def neg (A : Formula α) : Formula α := A 🡒 ⊥
scoped[Modal] prefix:75 "∼" => Formula.neg

def verum : Formula α := ∼⊥

instance : Top (Formula α) := ⟨verum⟩

def and (A B : Formula α) : Formula α := ∼(A 🡒 ∼B)
scoped[Modal] infixr:69 " ⋏ " => Formula.and

def or (A B : Formula α) : Formula α := ∼A 🡒 B
scoped[Modal] infixr:68 " ⋎ " => Formula.or

/-! ### Subformulas -/

variable [DecidableEq α] {A B : Formula α}

/-- The subformulas of a formula, the formula itself included. -/
@[grind]
def subfmls : Formula α → FormulaFinset α
  | .atom a  => {.atom a}
  | .falsum  => {⊥}
  | .imp A B => insert (A 🡒 B) (A.subfmls ∪ B.subfmls)
  | .box A   => insert (□A) A.subfmls

@[simp, grind .] lemma mem_subfmls_self (A : Formula α) : A ∈ A.subfmls := by
  cases A <;> simp [subfmls]

@[grind →] lemma subfmls_subset_of_mem (h : B ∈ A.subfmls) : B.subfmls ⊆ A.subfmls := by
  induction A with
  | atom a | falsum => simp_all [subfmls]
  | imp A₁ A₂ ih₁ ih₂ => grind [subfmls]
  | box A ih => grind [subfmls]

end Formula

namespace FormulaFinset

variable {α : Type*}

/-- `Λ` is closed under taking immediate subformulas. -/
structure SubformulaClosed (Λ : FormulaFinset α) : Prop where
  imp : ∀ {A B}, A 🡒 B ∈ Λ → A ∈ Λ ∧ B ∈ Λ
  box : ∀ {A}, □A ∈ Λ → A ∈ Λ

attribute [grind →] SubformulaClosed.imp SubformulaClosed.box

variable [DecidableEq α] {Γ : FormulaFinset α}

/-- The subformulas of the formulas in `Γ`. -/
@[grind]
def subfmls (Γ : FormulaFinset α) : FormulaFinset α := Γ.biUnion Formula.subfmls

@[grind .] lemma subset_subfmls : Γ ⊆ Γ.subfmls := by grind

@[grind .] lemma subformulaClosed_subfmls : Γ.subfmls.SubformulaClosed := by
  constructor <;> grind

end FormulaFinset

end Modal

end
