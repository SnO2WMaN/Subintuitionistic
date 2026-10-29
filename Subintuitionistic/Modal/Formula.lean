module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Image

/-!
# Modal formulas

Formulas built from variables and `⊥` with `🡒` and `□`; `∼`, `⋏`, `⋎` and `⊤` are abbreviations.
The connectives share their notation with propositional formulas (`Propositional.Formula`); the
notation is scoped to the namespace `Modal`, and the expected type tells the two apart.
-/

@[expose] public section

namespace Modal

inductive Formula (α : Type*) where
  | atom   : α → Formula α
  | falsum : Formula α
  | imp    : Formula α → Formula α → Formula α
  | box    : Formula α → Formula α
  deriving DecidableEq

abbrev FormulaSet (α : Type*) := Set (Formula α)

abbrev FormulaFinset (α : Type*) := Finset (Formula α)

abbrev Logic (α : Type*) := Set (Formula α)

namespace Formula

variable {α : Type*}

instance : Bot (Formula α) := ⟨falsum⟩

scoped[Modal] prefix:max "#" => Formula.atom
scoped[Modal] infixr:60 " 🡒 " => Formula.imp
scoped[Modal] prefix:76 "□" => Formula.box

@[simp] lemma falsum_eq : (falsum : Formula α) = ⊥ := rfl

@[grind =] lemma bot_eq_falsum : (⊥ : Formula α) = falsum := rfl

lemma box_injective : Function.Injective (box : Formula α → Formula α) := fun _ _ ↦ box.inj

/-- Recursion on formulas, with the cases written in notation. -/
@[elab_as_elim, induction_eliminator]
def rec' {motive : Formula α → Sort*} (atom : ∀ a, motive (#a)) (falsum : motive ⊥)
    (imp : ∀ A B, motive A → motive B → motive (A 🡒 B)) (box : ∀ A, motive A → motive (□A)) :
    ∀ A, motive A
  | .atom a  => atom a
  | .falsum  => falsum
  | .imp A B => imp A B (rec' atom falsum imp box A) (rec' atom falsum imp box B)
  | .box A   => box A (rec' atom falsum imp box A)

/-- Case analysis on formulas, with the cases written in notation. -/
@[elab_as_elim, cases_eliminator]
def cases' {motive : Formula α → Sort*} (atom : ∀ a, motive (#a)) (falsum : motive ⊥)
    (imp : ∀ A B, motive (A 🡒 B)) (box : ∀ A, motive (□A)) : ∀ A, motive A
  | .atom a  => atom a
  | .falsum  => falsum
  | .imp A B => imp A B
  | .box A   => box A

def unbox : Formula α → Option (Formula α)
  | .box A => some A
  | _      => none

@[simp, grind =] lemma unbox_eq_some {A B : Formula α} : A.unbox = some B ↔ A = □B := by
  cases A <;> simp [unbox, eq_comm]

def neg (A : Formula α) : Formula α := A 🡒 ⊥
scoped[Modal] prefix:75 "∼" => Formula.neg

@[grind =] lemma neg_eq (A : Formula α) : ∼A = A 🡒 ⊥ := rfl

def verum : Formula α := ∼⊥

instance : Top (Formula α) := ⟨verum⟩

def and (A B : Formula α) : Formula α := ∼(A 🡒 ∼B)
scoped[Modal] infixr:69 " ⋏ " => Formula.and

def or (A B : Formula α) : Formula α := ∼A 🡒 B
scoped[Modal] infixr:68 " ⋎ " => Formula.or

/-! ### Subformulas -/

variable [DecidableEq α] {A B : Formula α}

/-- The formula itself is included. -/
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

structure SubformulaClosed (Λ : FormulaFinset α) : Prop where
  imp : ∀ {A B}, A 🡒 B ∈ Λ → A ∈ Λ ∧ B ∈ Λ
  box : ∀ {A}, □A ∈ Λ → A ∈ Λ

attribute [grind →] SubformulaClosed.imp SubformulaClosed.box

def prebox (Γ : FormulaFinset α) : FormulaFinset α :=
  Γ.filterMap Formula.unbox fun _ _ _ h₁ h₂ ↦
    (Formula.unbox_eq_some.mp (Option.mem_def.mp h₁)).trans
      (Formula.unbox_eq_some.mp (Option.mem_def.mp h₂)).symm

variable [DecidableEq α] {Γ Δ : FormulaFinset α}

@[grind]
def subfmls (Γ : FormulaFinset α) : FormulaFinset α := Γ.biUnion Formula.subfmls

@[grind .] lemma subset_subfmls : Γ ⊆ Γ.subfmls := by grind

@[grind .] lemma subformulaClosed_subfmls : Γ.subfmls.SubformulaClosed := by
  constructor <;> grind

def box (Γ : FormulaFinset α) : FormulaFinset α := Γ.image Formula.box

@[simp, grind =] lemma mem_box {A : Formula α} : A ∈ Γ.box ↔ ∃ B ∈ Γ, □B = A := Finset.mem_image

@[simp, grind =] lemma box_empty : (∅ : FormulaFinset α).box = ∅ := Finset.image_empty _

@[simp, grind =] lemma box_union : (Γ ∪ Δ).box = Γ.box ∪ Δ.box := Finset.image_union _ _

@[simp, grind =] lemma box_image {β : Type*} (f : β → Formula α) (I : Finset β) :
    FormulaFinset.box (I.image f) = I.image fun x ↦ □f x := Finset.image_image

omit [DecidableEq α] in
@[simp, grind =] lemma mem_prebox {A : Formula α} : A ∈ Γ.prebox ↔ □A ∈ Γ := by
  simp [prebox]

end FormulaFinset

end Modal

end
