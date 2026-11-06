module

public import Subintuitionistic.Propositional.Kripke.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# `ω`-extensions
-/

@[expose] public section

namespace Propositional.Model

variable {κ α : Type*}

/-- The finite points of the chain form the tail and `⊤` is the bottom.
- [KKIM25, Definition 2.2] -/
def ωExtension (M : Model κ α) (r : M.World) (V : α → Prop) : Model (κ ⊕ ℕ∞) α where
  Rel'
    | .inl x, .inl y => M.Rel x y
    | .inl _, .inr _ => False
    | .inr _, .inl y => y = r ∨ r ≺ y
    | .inr i, .inr j => j < i
  Val'
    | .inl x, a => M x a
    | .inr i, a => M r a ∧ (i = ⊤ → V a)
  hereditary' := by
    rintro (x | i) (y | j) Rxy a h
    · exact M.hereditary Rxy h
    · exact Rxy.elim
    · rcases Rxy with rfl | Rry
      · exact h.1
      · exact M.hereditary Rry h.1
    · exact ⟨h.1, fun hj ↦ absurd Rxy (hj ▸ not_top_lt)⟩

namespace ωExtension

open World

variable {M : Model κ α} {r x y : M.World} {V : α → Prop} {i j : ℕ∞} {A : Formula α}

@[simp, grind =] lemma rel_inl_inl : (M.ωExtension r V).Rel (.inl x) (.inl y) ↔ x ≺ y := Iff.rfl

@[simp, grind .] lemma not_rel_inl_inr : ¬(M.ωExtension r V).Rel (.inl x) (.inr i) := id

@[simp, grind =]
lemma rel_inr_inl : (M.ωExtension r V).Rel (.inr i) (.inl y) ↔ y = r ∨ r ≺ y := Iff.rfl

@[simp, grind =] lemma rel_inr_inr : (M.ωExtension r V).Rel (.inr i) (.inr j) ↔ j < i := Iff.rfl

@[simp, grind =]
lemma val_inr {a : α} : (M.ωExtension r V) (.inr i) a ↔ M r a ∧ (i = ⊤ → V a) := Iff.rfl

lemma forces_inl : Sum.inl x ⊩[M.ωExtension r V] A ↔ x ⊩ A := by
  induction A generalizing x with
  | atom | falsum => rfl
  | and | or | imp => grind

lemma forces_of_forces_inr (h : Sum.inr i ⊩[M.ωExtension r fun a ↦ M r a] A) : r ⊩ A := by
  induction A with
  | atom a => exact h.1
  | falsum => exact h
  | and A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩
  | or A B ihA ihB => exact h.imp ihA ihB
  | imp A B =>
    exact fun x Rrx hB ↦
      forces_inl.mp (h (.inl x) (rel_inr_inl.mpr (.inr Rrx)) (forces_inl.mpr hB))

lemma rel_inr_succ (n : ℕ) : (M.ωExtension r V).Rel (.inr ((n + 1 : ℕ) : ℕ∞)) (.inr n) :=
  rel_inr_inr.mpr (by exact_mod_cast n.lt_succ_self)

variable (M r V) in
def chain : (M.ωExtension r V).InfiniteDescendingChain := ⟨fun n ↦ .inr n, rel_inr_succ⟩

lemma convergesTo_top : (chain M r V).ConvergesTo (.inr ⊤) where
  rel n := rel_inr_inr.mpr (ENat.natCast_lt_top n)
  eventually_rel := by
    rintro (y | j) h
    · exact .of_forall fun _ ↦ h
    · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (rel_inr_inr.mp h))
      exact Filter.eventually_atTop.mpr ⟨m + 1, fun n hn ↦ rel_inr_inr.mpr (by exact_mod_cast hn)⟩

instance [M.IsFPL] : (M.ωExtension r V).IsFPL where
  trans x y z := by
    rcases x with x | i <;> rcases y with y | j <;> rcases z with z | k <;>
      grind [IsTrans.trans (r := M.Rel), lt_trans]
  converseWellFounded := by
    have hinl (x : M.World) : Acc (Function.swap (M.ωExtension r V).Rel) (.inl x) := by
      induction x using (IsFPL.converseWellFounded (M := M)).induction with
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

end Propositional.Model

end
