module

public import Subintuitionistic.Modal.Kripke
public import Mathlib.Data.ENat.Basic

/-!
# Tails

`M.attachTail r V` attaches below the point `r` of `M` a descending chain indexed by `ℕ∞`: the
point `i` of the chain sees the points `j < i` of the chain, `r` and the points that `r` sees, and
forces the variables `V i`. The points of `M` keep their forcing, and the attached model is
again transitive and conversely well-founded.
-/

@[expose] public section

namespace Modal.Model

variable {κ α : Type*}

/-- The finite points of the chain form the tail and `⊤` is the bottom.
- [KKIM25, Definition 2.2] -/
def attachTail (M : Model κ α) (r : M.World) (V : ℕ∞ → α → Prop) : Model (κ ⊕ ℕ∞) α where
  Rel'
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl y => y = r ∨ M.Rel r y
    | .inr i, .inr j => j < i
  Val'
    | .inl x, a => M x a
    | .inr i, a => V i a

namespace attachTail

open World

variable {M : Model κ α} {r x y : M.World} {V : ℕ∞ → α → Prop} {i j : ℕ∞} {A : Formula α}

@[simp, grind =] lemma rel_inl_inl : (M.attachTail r V).Rel (.inl x) (.inl y) ↔ x ≺ y := Iff.rfl

@[simp, grind .] lemma not_rel_inl_inr : ¬(M.attachTail r V).Rel (.inl x) (.inr i) := id

@[simp, grind =] lemma rel_inr_inl : (M.attachTail r V).Rel (.inr i) (.inl y) ↔ y = r ∨ r ≺ y :=
  Iff.rfl

@[simp, grind =] lemma rel_inr_inr : (M.attachTail r V).Rel (.inr i) (.inr j) ↔ j < i := Iff.rfl

@[simp, grind =] lemma val_inr {a : α} : (M.attachTail r V) (.inr i) a ↔ V i a := Iff.rfl

lemma forces_inl : Sum.inl x ⊩[M.attachTail r V] A ↔ x ⊩ A := by
  induction A generalizing x with
  | atom | falsum => rfl
  | imp A B ihA ihB => exact imp_congr ihA ihB
  | box A ih =>
    constructor
    · intro h y Rxy
      exact ih.mp (h (.inl y) Rxy)
    · rintro h (y | j) Rxy
      · exact ih.mpr (h y Rxy)
      · exact absurd Rxy not_rel_inl_inr

instance [IsTrans _ M.Rel] : IsTrans _ (M.attachTail r V).Rel where
  trans x y z := by
    rcases x with x | i <;> rcases y with y | j <;> rcases z with z | k <;>
      grind [IsTrans.trans (r := M.Rel), lt_trans]

instance [M.IsGL] : (M.attachTail r V).IsGL where
  converseWellFounded := by
    have hinl (x : M.World) : Acc (Function.swap (M.attachTail r V).Rel) (.inl x) := by
      induction x using (IsGL.converseWellFounded (M := M)).induction with
      | h x ih =>
        constructor
        rintro (y | j) Rxy
        · exact ih y Rxy
        · exact absurd Rxy not_rel_inl_inr
    constructor
    rintro (x | i)
    · exact hinl x
    · induction i using WellFoundedLT.induction with
      | ind i ih =>
        constructor
        rintro (y | j) Rij
        · exact hinl y
        · exact ih j Rij

end attachTail

end Modal.Model

end
