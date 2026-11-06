module

public import Subintuitionistic.Modal.Kripke.Basic
public import Mathlib.Data.ENat.Basic

/-!
# `ω`-extensions
-/

@[expose] public section

namespace Modal.Model

variable {κ α : Type*}

/-- The finite points of the chain form the tail and `⊤` is the bottom.
- [KKIM25, Definition 2.2] -/
def ωExtension (M : Model κ α) (r : M.World) (V : ℕ∞ → α → Prop) : Model (κ ⊕ ℕ∞) α where
  Rel'
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl y => y = r ∨ M.Rel r y
    | .inr i, .inr j => j < i
  Val'
    | .inl x, a => M x a
    | .inr i, a => V i a

namespace ωExtension

open World

variable {M : Model κ α} {r x y : M.World} {V : ℕ∞ → α → Prop} {i j : ℕ∞} {A : Formula α}

@[simp, grind =] lemma rel_inl_inl : (M.ωExtension r V).Rel (.inl x) (.inl y) ↔ x ≺ y := Iff.rfl

@[simp, grind .] lemma not_rel_inl_inr : ¬(M.ωExtension r V).Rel (.inl x) (.inr i) := id

@[simp, grind =] lemma rel_inr_inl : (M.ωExtension r V).Rel (.inr i) (.inl y) ↔ y = r ∨ r ≺ y :=
  Iff.rfl

@[simp, grind =] lemma rel_inr_inr : (M.ωExtension r V).Rel (.inr i) (.inr j) ↔ j < i := Iff.rfl

@[simp, grind =] lemma val_inr {a : α} : (M.ωExtension r V) (.inr i) a ↔ V i a := Iff.rfl

lemma forces_inl : Sum.inl x ⊩[M.ωExtension r V] A ↔ x ⊩ A := by
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

lemma rel_inr_succ (n : ℕ) : (M.ωExtension r V).Rel (.inr ((n + 1 : ℕ) : ℕ∞)) (.inr n) :=
  rel_inr_inr.mpr (by exact_mod_cast n.lt_succ_self)

lemma convergesTo_top : (M.ωExtension r V).ConvergesTo (fun n : ℕ ↦ .inr n) (.inr ⊤) where
  rel n := rel_inr_inr.mpr (ENat.natCast_lt_top n)
  eventually_rel := by
    rintro (y | j) h
    · exact .of_forall fun _ ↦ h
    · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (rel_inr_inr.mp h))
      exact Filter.eventually_atTop.mpr ⟨m + 1, fun n hn ↦ rel_inr_inr.mpr (by exact_mod_cast hn)⟩

instance [IsTrans _ M.Rel] : IsTrans _ (M.ωExtension r V).Rel where
  trans x y z := by
    rcases x with x | i <;> rcases y with y | j <;> rcases z with z | k <;>
      grind [IsTrans.trans (r := M.Rel), lt_trans]

instance [M.IsGL] : (M.ωExtension r V).IsGL where
  converseWellFounded := by
    have hinl (x : M.World) : Acc (Function.swap (M.ωExtension r V).Rel) (.inl x) := by
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

end ωExtension

end Modal.Model

end
