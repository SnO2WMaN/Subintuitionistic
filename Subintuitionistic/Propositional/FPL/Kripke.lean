module

public import Subintuitionistic.Propositional.FPL.Basic
public import Subintuitionistic.Propositional.Kripke
public import Mathlib.Basic.Finite.Prod

/-!
# Kripke soundness and completeness of `FPL`

`⊢ᴳ[𝐅𝐏𝐋] S ↔ ∀ M, [M.IsFPL] → M ⊧ S` (`logicFPL.Derivable.iff_valid`). The countermodel of an
unprovable sequent is `countermodel`, whose points are `SaturatedSequent`s.
-/

@[expose] public section

namespace Propositional.logicFPL.Derivable

open Model Model.World

variable {κ α : Type*} [DecidableEq α]

section

variable {M : Model κ α}

/-- The rule `impR` preserves validity in an FPL model. -/
lemma forces_imp_of_forces_premises [M.IsFPL] {Θ : FormulaFinset α}
    {P : Finset (Formula α × Formula α)} {A B : Formula α}
    (ih : ∀ I ⊆ P, M ⊧ (insert (A 🡒 B) (insert A (Θ ∪ I.image Prod.snd)) ⟹
      insert B ((P \ I).image Prod.fst)))
    {x : M.World} (hx : ∀ C ∈ Θ ∪ imps P, x ⊩ C) : x ⊩ A 🡒 B := by
  classical
  have wf : WellFounded (Function.swap M.Rel) := Finite.wellFounded_of_trans_of_irrefl _
  induction x using wf.induction with
  | _ x ihx =>
    intro y Rxy hyA
    have hy : ∀ C ∈ Θ ∪ imps P, y ⊩ C := fun C hC ↦ forces_of_rel Rxy (hx C hC)
    have hyAB : y ⊩ A 🡒 B := ihx y Rxy hy
    obtain ⟨C, hC, hyC⟩ := ih (P.filter fun p ↦ y ⊩ p.2) (Finset.filter_subset _ _) y <| by
      intro D hD
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hyAB
      rcases Finset.mem_insert.mp hD with rfl | hD
      · exact hyA
      rcases Finset.mem_union.mp hD with hD | hD
      · exact hy D (Finset.mem_union_left _ hD)
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hD
        exact (Finset.mem_filter.mp hp).2
    have hP : ∀ p ∈ P, x ⊩ p.1 🡒 p.2 := fun p hp ↦
      hx _ <| Finset.mem_union_right _ <| Finset.mem_image_of_mem _ hp
    rcases Finset.mem_insert.mp hC with rfl | hC
    · exact hyC
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hC
      obtain ⟨hpP, hpy⟩ := Finset.mem_sdiff.mp hp
      exact (hpy <| Finset.mem_filter.mpr ⟨hpP, hP p hpP y Rxy hyC⟩).elim

end

/-- - [IKK01, Theorem 3.2] -/
theorem sound {S : Sequent α} (M : Model κ α) [M.IsFPL] (h : ⊢ᴳ[𝐅𝐏𝐋] S) : M ⊧ S := by
  intro x
  induction h generalizing x with
  | axm A => exact fun hx ↦ ⟨A, by simp, hx A (by simp)⟩
  | botL => exact fun hx ↦ absurd (hx ⊥ (by simp)) not_forces_bot
  | wkL _ hΓ ih => exact fun hx ↦ ih x fun A hA ↦ hx A (hΓ hA)
  | wkR _ hΔ ih => exact fun hx ↦ by grind [ForcesSequent, ih x hx]
  | andL _ ih => simp_all [ForcesSequent]
  | @andR Γ Δ A B _ _ ih₁ ih₂ =>
    intro hx
    obtain ⟨C, hC, hxC⟩ := ih₁ x hx
    obtain ⟨D, hD, hxD⟩ := ih₂ x hx
    have : x ⊩ A ⋏ B ∨ ∃ E ∈ Δ, x ⊩ E := by grind
    obtain h | ⟨E, hE, hxE⟩ := this
    · exact ⟨A ⋏ B, by simp, h⟩
    · exact ⟨E, by simp [hE], hxE⟩
  | @orL _ _ A B _ _ ih₁ ih₂ =>
    intro hx
    rcases hx (A ⋎ B) (by simp) with h | h
    · exact ih₁ x (by simp_all)
    · exact ih₂ x (by simp_all)
  | @orR Γ Δ A B _ ih =>
    intro hx
    obtain ⟨C, hC, hxC⟩ := ih x hx
    have : x ⊩ A ⋎ B ∨ ∃ D ∈ Δ, x ⊩ D := by grind
    obtain h | ⟨D, hD, hxD⟩ := this
    · exact ⟨A ⋎ B, by simp, h⟩
    · exact ⟨D, by simp [hD], hxD⟩
  | impR _ ih => exact fun hx ↦ ⟨_, by simp, forces_imp_of_forces_premises ih hx⟩

end Propositional.logicFPL.Derivable

namespace Propositional.logicFPL

open Model Model.World

variable {α : Type*} [DecidableEq α] {Λ : FormulaFinset α} {S : Sequent α} {A : Formula α}

/-- The points of the countermodel.
- [IKK01, Definition 2.5] -/
structure SaturatedSequent (Λ : FormulaFinset α) extends Sequent α where
  saturated : toSequent.Saturated
  subset : toSequent ⊆ (Λ ⟹ Λ)
  unprovable : ⊬ᴳ[𝐅𝐏𝐋] toSequent

namespace SaturatedSequent

@[ext] lemma ext {x y : SaturatedSequent Λ} (ha : x.ant = y.ant) (hs : x.suc = y.suc) : x = y := by
  obtain ⟨⟨_, _⟩, _⟩ := x
  obtain ⟨⟨_, _⟩, _⟩ := y
  simp_all

instance : Finite (SaturatedSequent Λ) :=
  Finite.of_injective (β := Λ.powerset × Λ.powerset)
    (fun x ↦ (⟨x.ant, Finset.mem_powerset.mpr x.subset.1⟩,
      ⟨x.suc, Finset.mem_powerset.mpr x.subset.2⟩))
    fun _ _ h ↦ ext (congrArg (·.1.val) h) (congrArg (·.2.val) h)

section Maximal

variable {T U : Sequent α}

lemma derivable_of_not_subset
    (hmax : ∀ U, T ⊆ U → U ⊆ (Λ ⟹ Λ) → ⊬ᴳ[𝐅𝐏𝐋] U → U = T)
    (hTU : T ⊆ U) (hUΛ : U ⊆ (Λ ⟹ Λ)) (hne : ¬U ⊆ T) : ⊢ᴳ[𝐅𝐏𝐋] U := by
  by_contra h
  obtain rfl := hmax U hTU hUΛ h
  exact hne ⟨subset_rfl, subset_rfl⟩

variable {C : Formula α}

lemma derivable_insert_ant
    (hmax : ∀ U, T ⊆ U → U ⊆ (Λ ⟹ Λ) → ⊬ᴳ[𝐅𝐏𝐋] U → U = T)
    (hTΛ : T ⊆ (Λ ⟹ Λ)) (hC : C ∈ Λ) (hCT : C ∉ T.ant) : ⊢ᴳ[𝐅𝐏𝐋] insert C T.ant ⟹ T.suc :=
  derivable_of_not_subset hmax ⟨by grind, subset_rfl⟩ ⟨by grind, hTΛ.2⟩ (by grind)

lemma derivable_insert_suc
    (hmax : ∀ U, T ⊆ U → U ⊆ (Λ ⟹ Λ) → ⊬ᴳ[𝐅𝐏𝐋] U → U = T)
    (hTΛ : T ⊆ (Λ ⟹ Λ)) (hC : C ∈ Λ) (hCT : C ∉ T.suc) : ⊢ᴳ[𝐅𝐏𝐋] T.ant ⟹ insert C T.suc :=
  derivable_of_not_subset hmax ⟨subset_rfl, by grind⟩ ⟨hTΛ.1, by grind⟩ (by grind)

variable (hΛ : Λ.SubformulaClosed) (hTΛ : T ⊆ (Λ ⟹ Λ)) (hT : ⊬ᴳ[𝐅𝐏𝐋] T)
  (hmax : ∀ U, T ⊆ U → U ⊆ (Λ ⟹ Λ) → ⊬ᴳ[𝐅𝐏𝐋] U → U = T)
include hΛ hTΛ hT hmax

lemma andL_of_maximal {A B : Formula α} (h : A ⋏ B ∈ T.ant) : A ∈ T.ant ∧ B ∈ T.ant := by
  obtain ⟨hA, hB⟩ := hΛ.and (hTΛ.1 h)
  by_contra hn
  apply hT
  have hd := derivable_of_not_subset hmax (U := insert A (insert B T.ant) ⟹ T.suc)
    ⟨by grind, subset_rfl⟩ ⟨by grind, hTΛ.2⟩ (by grind)
  exact (Derivable.andL hd).wk (by grind) subset_rfl

lemma andR_of_maximal {A B : Formula α} (h : A ⋏ B ∈ T.suc) : A ∈ T.suc ∨ B ∈ T.suc := by
  obtain ⟨hA, hB⟩ := hΛ.and (hTΛ.2 h)
  by_contra hn
  apply hT
  have h₁ := derivable_insert_suc hmax hTΛ hA (by grind)
  have h₂ := derivable_insert_suc hmax hTΛ hB (by grind)
  exact (Derivable.andR h₁ h₂).wk subset_rfl (by grind)

lemma orL_of_maximal {A B : Formula α} (h : A ⋎ B ∈ T.ant) : A ∈ T.ant ∨ B ∈ T.ant := by
  obtain ⟨hA, hB⟩ := hΛ.or (hTΛ.1 h)
  by_contra hn
  apply hT
  have h₁ := derivable_insert_ant hmax hTΛ hA (by grind)
  have h₂ := derivable_insert_ant hmax hTΛ hB (by grind)
  exact (Derivable.orL h₁ h₂).wk (by grind) subset_rfl

lemma orR_of_maximal {A B : Formula α} (h : A ⋎ B ∈ T.suc) : A ∈ T.suc ∧ B ∈ T.suc := by
  obtain ⟨hA, hB⟩ := hΛ.or (hTΛ.2 h)
  by_contra hn
  apply hT
  have hd := derivable_of_not_subset hmax (U := T.ant ⟹ insert A (insert B T.suc))
    ⟨subset_rfl, by grind⟩ ⟨hTΛ.1, by grind⟩ (by grind)
  exact (Derivable.orR hd).wk subset_rfl (by grind)

end Maximal

/-- - [IKK01, Lemma 2.6] -/
lemma lindenbaum (hΛ : Λ.SubformulaClosed) (hS : S ⊆ (Λ ⟹ Λ)) (h : ⊬ᴳ[𝐅𝐏𝐋] S) :
    ∃ x : SaturatedSequent Λ, S ⊆ x.toSequent := by
  obtain ⟨T, hST, hTΛ, hT, hmax⟩ := Sequent.exists_maximal (fun S ↦ ⊢ᴳ[𝐅𝐏𝐋] S) hS h
  exact ⟨⟨T, ⟨andL_of_maximal hΛ hTΛ hT hmax, andR_of_maximal hΛ hTΛ hT hmax,
    orL_of_maximal hΛ hTΛ hT hmax, orR_of_maximal hΛ hTΛ hT hmax⟩, hTΛ, hT⟩, hST⟩

end SaturatedSequent

open SaturatedSequent

/-- - [IKK01, Theorem 3.3] -/
def countermodel (Λ : FormulaFinset α) : Model (SaturatedSequent Λ) α where
  Rel' x y := x.ant ⊂ y.ant ∧ ∀ C D, C 🡒 D ∈ x.ant → C ∈ y.suc ∨ D ∈ y.ant
  Val' x a := #a ∈ x.ant
  hereditary' Rxy _ ha := Rxy.1.subset ha

namespace countermodel

instance : (countermodel Λ).IsFPL where
  trans _ _ _ Rxy Ryz := ⟨Rxy.1.trans Ryz.1, fun C D h ↦ Ryz.2 C D (Rxy.1.subset h)⟩
  irrefl _ Rxx := lt_irrefl _ Rxx.1

section Successor

variable {E F : Formula α}

def impPairs (x : SaturatedSequent Λ) : Finset (Formula α × Formula α) :=
  (Λ ×ˢ Λ).filter fun p ↦ p.1 🡒 p.2 ∈ x.ant

lemma mem_impPairs (hΛ : Λ.SubformulaClosed) {x : SaturatedSequent Λ} {C D : Formula α} :
    (C, D) ∈ impPairs x ↔ C 🡒 D ∈ x.ant := by
  have h : C 🡒 D ∈ x.ant → C ∈ Λ ∧ D ∈ Λ := fun h ↦ hΛ.imp (x.subset.1 h)
  grind [impPairs]

lemma imps_impPairs_subset (x : SaturatedSequent Λ) : imps (impPairs x) ⊆ x.ant := by
  grind [imps, impPairs]

lemma exists_unprovable_premise {x : SaturatedSequent Λ} (h : E 🡒 F ∈ x.suc) :
    ∃ I ⊆ impPairs x, ⊬ᴳ[𝐅𝐏𝐋] (insert (E 🡒 F) (insert E (x.ant ∪ I.image Prod.snd))
      ⟹ insert F ((impPairs x \ I).image Prod.fst)) := by
  by_contra hcon
  push Not at hcon
  have h₁ := Derivable.impR (Θ := x.ant) (P := impPairs x) (A := E) (B := F) hcon
  exact x.unprovable <| h₁.wk (Finset.union_subset subset_rfl (imps_impPairs_subset x))
    (Finset.singleton_subset_iff.mpr h)

lemma exists_rel_of_imp_mem_suc (hΛ : Λ.SubformulaClosed) {x : (countermodel Λ).World}
    (h : E 🡒 F ∈ x.suc) : ∃ y : (countermodel Λ).World, x ≺ y ∧ E ∈ y.ant ∧ F ∈ y.suc := by
  obtain ⟨hE, hF⟩ := hΛ.imp (x.subset.2 h)
  obtain ⟨I, hIP, hI⟩ := exists_unprovable_premise h
  have hP : ∀ p ∈ impPairs x, p.1 ∈ Λ ∧ p.2 ∈ Λ := fun p hp ↦ by grind [impPairs]
  have hΛ' : (insert (E 🡒 F) (insert E (x.ant ∪ I.image Prod.snd))
      ⟹ insert F ((impPairs x \ I).image Prod.fst)) ⊆ (Λ ⟹ Λ) := by
    have h₁ := x.subset.1
    have h₂ := x.subset.2
    and_intros
    · grind
    · grind
  obtain ⟨y, hy⟩ := lindenbaum hΛ hΛ' hI
  have Rxy : x ≺ y := by
    change x.ant ⊂ y.ant ∧ ∀ C D, C 🡒 D ∈ x.ant → C ∈ y.suc ∨ D ∈ y.ant
    constructor
    · exact (Finset.ssubset_iff_of_subset (by grind)).mpr
        ⟨E 🡒 F, by grind, fun hmem ↦ x.unprovable (Derivable.union hmem h)⟩
    · intro C D hCD
      have hCD' := (mem_impPairs hΛ).mpr hCD
      obtain ⟨hy₁, hy₂⟩ := hy
      by_cases hpI : (C, D) ∈ I
      · exact Or.inr <| hy₁ <| by grind
      · exact Or.inl <| hy₂ <| Finset.mem_insert_of_mem <|
        Finset.mem_image.mpr ⟨(C, D), Finset.mem_sdiff.mpr ⟨hCD', hpI⟩, rfl⟩
  exact ⟨y, Rxy, hy.1 (by simp), hy.2 (by simp)⟩

end Successor

/-- - [IKK01, Theorem 3.3] -/
lemma truthlemma (hΛ : Λ.SubformulaClosed) (x : (countermodel Λ).World) :
    (A ∈ x.ant → x ⊩ A) ∧ (A ∈ x.suc → x ⊮ A) := by
  induction A generalizing x with
  | atom a => exact ⟨fun h ↦ h, fun h hx ↦ x.unprovable (Derivable.union hx h)⟩
  | falsum => exact ⟨fun h ↦ (x.unprovable (Derivable.botL_mem h)).elim, fun _ ↦ not_forces_bot⟩
  | and A B ihA ihB =>
    obtain ⟨h₁, h₂, -, -⟩ := x.saturated
    grind
  | or A B ihA ihB =>
    obtain ⟨-, -, h₁, h₂⟩ := x.saturated
    grind
  | imp E F ihE ihF =>
    constructor
    · intro h y Rxy hyE
      rcases Rxy.2 E F h with hE | hF
      · exact ((ihE y).2 hE hyE).elim
      · exact (ihF y).1 hF
    · intro h hx
      obtain ⟨y, Rxy, hE, hF⟩ := exists_rel_of_imp_mem_suc hΛ h
      exact (ihF y).2 hF (hx y Rxy ((ihE y).1 hE))

end countermodel

namespace Derivable

universe u

variable {α : Type u} [DecidableEq α] {S : Sequent α}

/-- - [IKK01, Theorem 3.3] -/
theorem complete (h : ∀ {κ : Type u} (M : Model κ α), [M.IsFPL] → M ⊧ S) : ⊢ᴳ[𝐅𝐏𝐋] S := by
  by_contra hS
  obtain ⟨x, hx⟩ := lindenbaum Sequent.subformulaClosed_subfmls Sequent.subset_subfmls hS
  obtain ⟨D, hD, hxD⟩ := h (countermodel S.subfmls) x
    fun C hC ↦ (countermodel.truthlemma Sequent.subformulaClosed_subfmls x).1 (hx.1 hC)
  exact (countermodel.truthlemma Sequent.subformulaClosed_subfmls x).2 (hx.2 hD) hxD

/-- - [IKK01, Theorem 3.2, Theorem 3.3] -/
theorem iff_valid : ⊢ᴳ[𝐅𝐏𝐋] S ↔ ∀ {κ : Type u} (M : Model κ α), [M.IsFPL] → M ⊧ S :=
  ⟨fun h _ M _ ↦ sound M h, complete⟩

end Derivable

end Propositional.logicFPL

end
