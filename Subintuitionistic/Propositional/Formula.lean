module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Preimage

/-!
# Propositional formulas
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

def neg (A : Formula α) : Formula α := A 🡒 ⊥
scoped[Propositional] prefix:75 "∼" => Formula.neg

@[simp, grind =] lemma neg_eq (A : Formula α) : ∼A = A 🡒 ⊥ := rfl

instance : Top (Formula α) := ⟨∼⊥⟩

@[simp, grind =] lemma top_eq : (⊤ : Formula α) = ∼⊥ := rfl

@[grind =] lemma bot_eq_falsum : (⊥ : Formula α) = falsum := rfl

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

variable {α : Type*} {A B : Formula α}

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

/-! ### Implications of pairs -/

def imps (P : Finset (Formula α × Formula α)) : FormulaFinset α := P.image fun p ↦ p.1 🡒 p.2

@[grind ←]
lemma mem_imps_of_mem {P : Finset _} (h : (A, B) ∈ P) : A 🡒 B ∈ imps P :=
  Finset.mem_image_of_mem _ h

lemma exists_imps (Γ : FormulaFinset α) :
    ∃ P : Finset _, imps P ⊆ Γ ∧ ∀ A B, A 🡒 B ∈ Γ → (A, B) ∈ P := by
  have hf : Function.Injective fun p : Formula α × Formula α ↦ p.1 🡒 p.2 :=
    fun p q hpq ↦ by grind
  exact ⟨Γ.preimage _ hf.injOn, fun x ↦ by grind [imps, Finset.mem_preimage], by simp⟩

end FormulaFinset

end Propositional

end
