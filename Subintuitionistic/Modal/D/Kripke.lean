module

public import Subintuitionistic.Modal.D.Basic
public import Subintuitionistic.Modal.GL.Kripke
public import Subintuitionistic.Modal.Tail
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite

/-!
# Kripke semantics and cut admissibility for `D`

`iff_GL` identifies the level `0` of `logicD` with `logicGL`. The levels `1` and `2` are
characterized by forcing along descending chains of transitive conversely well-founded models
(`eventually_forces`, `complete₁`, `forces_of_level₂`, `complete₂`). `cut` is admissible at every
level.
-/

@[expose] public section

namespace Modal.logicD.Derivable

open Model Model.World Filter

universe u

variable {α : Type u} [DecidableEq α] {ℓ : Fin 3}
  {Γ Γ₁ Γ₂ Δ Δ₁ Δ₂ Λ : FormulaFinset α} {A : Formula α} {T : Sequent α}

/-! ### The level `0` -/

lemma toGL {S : LayeredSequent α} (h : ⊢ᴳ[𝐃] S) (hS : S.level = 0) : ⊢ᴳ[𝐆𝐋] S.toSequent := by
  induction h with
  | axm => exact .axm (Finset.mem_singleton_self _) (Finset.mem_singleton_self _)
  | botL => exact .botL (Finset.mem_singleton_self _)
  | wk _ hΓ hΔ ih => exact (ih hS).wk hΓ hΔ
  | impL _ _ ih₁ ih₂ =>
    exact .impL (Finset.mem_insert_self _ _) ((ih₁ hS).wk (Finset.subset_insert _ _) subset_rfl)
      ((ih₂ hS).wk (Finset.insert_subset_insert _ (Finset.subset_insert _ _)) subset_rfl)
  | impR _ ih =>
    exact .impR (Finset.mem_insert_self _ _)
      ((ih hS).wk subset_rfl (Finset.insert_subset_insert _ (Finset.subset_insert _ _)))
  | boxGL _ ih =>
    exact .boxGL subset_rfl (Finset.mem_singleton_self _)
      ((ih rfl).wk (Finset.insert_subset_insert _ (Finset.union_comm _ _).subset) subset_rfl)
  | boxL | liftUp₀₁ | liftUp₁₂ => nomatch hS

lemma ofGL {T : Sequent α} (h : ⊢ᴳ[𝐆𝐋] T) : ⊢ᴳ[𝐃] T.ant ⟹[0] T.suc := by
  induction h with
  | axm hA hB => exact union hA hB
  | botL h => exact botL_mem h
  | impL hAB _ _ ih₁ ih₂ => exact (impL ih₁ ih₂).wk (Finset.insert_subset hAB subset_rfl) subset_rfl
  | impR hAB _ ih => exact ih.impR.wk subset_rfl (Finset.insert_subset hAB subset_rfl)
  | boxGL hΘ hA _ ih =>
    exact (boxGL (ih.wk (Finset.insert_subset_insert _ (Finset.union_comm _ _).subset)
      subset_rfl)).wk hΘ (Finset.singleton_subset_iff.mpr hA)

/-- - [KKIM25, Theorem 4.1] -/
theorem iff_GL : ⊢ᴳ[𝐃] Γ ⟹[0] Δ ↔ ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ :=
  ⟨fun h ↦ toGL h rfl, ofGL⟩

/-! ### Saturation -/

/-- - [KKIM25, Lemma 5.3] -/
lemma exists_saturated (hΛ : Λ.SubformulaClosed) (hT : T ⊆ (Λ ⟹ Λ))
    (hd : ⊬ᴳ[𝐃] T.ant ⟹[ℓ] T.suc) :
    ∃ U, T ⊆ U ∧ U ⊆ (Λ ⟹ Λ) ∧ U.Saturated ∧ (⊬ᴳ[𝐃] U.ant ⟹[ℓ] U.suc) ∧
      (ℓ = 1 → ∀ {A}, □A ∈ U.ant → A ∈ U.ant) := by
  obtain ⟨U, h₁, h₂, h₃, hmax⟩ :=
    Sequent.exists_maximal (fun U ↦ ⊢ᴳ[𝐃] U.ant ⟹[ℓ] U.suc) hT hd
  have hbox : ℓ = 1 → ∀ {A}, □A ∈ U.ant → A ∈ U.ant := by
    rintro rfl A hA
    by_contra hA'
    by_cases d : ⊢ᴳ[𝐃] insert A U.ant ⟹[1] U.suc
    · exact h₃ ((boxL d).wk (Finset.insert_subset hA subset_rfl) subset_rfl)
    · have hAΛ := hΛ.box (h₂.1 hA)
      have e := hmax (insert A U.ant ⟹ U.suc) (by grind) (by grind) d
      exact hA' ((congrArg Sequent.ant e).subset (Finset.mem_insert_self _ _))
  have hsat := Sequent.saturated_of_maximal (fun U ↦ ⊢ᴳ[𝐃] U.ant ⟹[ℓ] U.suc) hΛ h₂ h₃ hmax
    (fun hAB d₁ d₂ ↦ (impL d₁ d₂).wk (Finset.insert_subset hAB subset_rfl) subset_rfl)
    (fun hAB d ↦ (impR d).wk subset_rfl (Finset.insert_subset hAB subset_rfl))
  exact ⟨U, h₁, h₂, hsat, h₃, hbox⟩

lemma exists_countermodel_world (hΛ : Λ.SubformulaClosed) (hT : T ⊆ (Λ ⟹ Λ))
    (hd : ⊬ᴳ[𝐃] T.ant ⟹[1] T.suc) :
    ∃ t : (logicGL.countermodel Λ).World, T ⊆ t.toSequent ∧ ∀ {A}, □A ∈ t.ant → A ∈ t.ant := by
  obtain ⟨U, h₁, h₂, h₃, h₄, h₅⟩ := exists_saturated hΛ hT hd
  exact ⟨⟨U, h₃, h₂, fun d ↦ h₄ (liftUp₀₁ (ofGL d))⟩, h₁, h₅ rfl⟩

/-! ### The level `1` -/

section

variable {κ : Type*} {M : Model κ α} {w : ℕ → M.World}

omit [DecidableEq α] in
lemma rel_of_lt [IsTrans _ M.Rel] (hw : ∀ n, w (n + 1) ≺ w n) {m n : ℕ} (hmn : m < n) :
    w n ≺ w m := by
  induction n, hmn using Nat.le_induction with
  | base => exact hw m
  | succ n _ ih => exact IsTrans.trans _ _ _ (hw n) ih

omit [DecidableEq α] in
lemma eventually_forces_box_imp [IsTrans _ M.Rel] (hw : ∀ n, w (n + 1) ≺ w n) (A : Formula α) :
    ∀ᶠ n in atTop, w n ⊩ □A 🡒 A := by
  by_cases h : ∀ n, w n ⊩ A
  · exact .of_forall fun n _ ↦ h n
  · obtain ⟨m, hm⟩ := not_forall.mp h
    exact eventually_atTop.mpr ⟨m + 1, fun n hn hA ↦ absurd (hA (w m) (rel_of_lt hw hn)) hm⟩

variable (M) in
/-- - [KKIM25, Theorem 5.6] -/
theorem eventually_forces [M.IsGL] (hw : ∀ n, w (n + 1) ≺ w n) {S : LayeredSequent α}
    (h : ⊢ᴳ[𝐃] S) (hS : S.level = 1) : ∀ᶠ n in atTop, w n ⊩ S.toSequent := by
  induction h with
  | axm => exact .of_forall fun _ h ↦ ⟨_, Finset.mem_singleton_self _, h _ (by simp)⟩
  | botL => exact .of_forall fun _ h ↦ (h _ (Finset.mem_singleton_self _)).elim
  | wk _ hΓ hΔ ih => exact (ih hS).mono fun _ hn ↦ forcesSequent_wk hn hΓ hΔ
  | impL _ _ ih₁ ih₂ => exact ((ih₁ hS).and (ih₂ hS)).mono fun _ hn ↦ forcesSequent_impL hn.1 hn.2
  | impR _ ih => exact (ih hS).mono fun _ hn ↦ forcesSequent_impR hn
  | @boxL _ _ A _ ih =>
    exact ((ih hS).and (eventually_forces_box_imp hw A)).mono fun _ hn ↦ by grind
  | liftUp₀₁ d => exact .of_forall fun n ↦ logicGL.Derivable.sound M (toGL d rfl) (w n)
  | boxGL | liftUp₁₂ => nomatch hS

end

lemma truthlemma_tail (hΛ : Λ.SubformulaClosed) {t : (logicGL.countermodel Λ).World}
    (hbox : ∀ {A}, □A ∈ t.ant → A ∈ t.ant) {V : ℕ∞ → α → Prop}
    (hV : ∀ (n : ℕ) a, V n a ↔ #a ∈ t.ant) (A : Formula α) (n : ℕ) :
    (A ∈ t.ant → Sum.inr (n : ℕ∞) ⊩[(logicGL.countermodel Λ).attachTail t V] A) ∧
      (A ∈ t.suc → Sum.inr (n : ℕ∞) ⊮[(logicGL.countermodel Λ).attachTail t V] A) := by
  induction A generalizing n with
  | atom a =>
    have := logicGL.countermodel.truthlemma hΛ t (A := #a)
    have := hV n a
    grind
  | falsum =>
    have := logicGL.countermodel.truthlemma hΛ t (A := ⊥)
    exact ⟨fun h ↦ (this.1 h).elim, fun _ ↦ not_forces_bot⟩
  | imp A B ihA ihB =>
    have := t.saturated
    have := ihA n
    have := ihB n
    grind
  | box A ih =>
    constructor
    · rintro hA (y | j) Rny
      · apply attachTail.forces_inl.mpr
        rcases attachTail.rel_inr_inl.mp Rny with rfl | Rty
        · exact (logicGL.countermodel.truthlemma hΛ _).1 (hbox hA)
        · exact (logicGL.countermodel.truthlemma hΛ y).1 (Rty.1 A hA).1
      · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (attachTail.rel_inr_inr.mp Rny))
        exact (ih m).1 (hbox hA)
    · intro hA hn
      obtain ⟨y, Rty, hy⟩ : ∃ y, t ≺ y ∧ y ⊮ A := by
        simpa using (logicGL.countermodel.truthlemma hΛ t).2 hA
      exact hy (attachTail.forces_inl.mp (hn (.inl y) (attachTail.rel_inr_inl.mpr (.inr Rty))))

/-- - [KKIM25, Theorem 5.6] -/
theorem complete₁
    (hc : ∀ {κ : Type u} (M : Model κ α) [M.IsGL] (w : ℕ → M.World),
      (∀ n, w (n + 1) ≺ w n) → ∃ n, w n ⊩ (Γ ⟹ Δ)) :
    ⊢ᴳ[𝐃] Γ ⟹[1] Δ := by
  by_contra hd
  have hΛ := Sequent.subformulaClosed_subfmls (S := Γ ⟹ Δ)
  obtain ⟨t, ht, hbox⟩ := exists_countermodel_world hΛ Sequent.subset_subfmls hd
  have key := truthlemma_tail hΛ hbox (V := fun _ a ↦ #a ∈ t.ant) fun _ _ ↦ Iff.rfl
  obtain ⟨n, hn⟩ := hc ((logicGL.countermodel (Γ ⟹ Δ).subfmls).attachTail t fun _ a ↦ #a ∈ t.ant)
    (fun n ↦ .inr n) fun n ↦ attachTail.rel_inr_inr.mpr (by exact_mod_cast n.lt_succ_self)
  obtain ⟨D, hD, hnD⟩ := hn fun C hC ↦ (key C n).1 (ht.1 hC)
  exact (key D n).2 (ht.2 hD) hnD

/-! ### The level `2` -/

section

variable {κ : Type*} (M : Model κ α) [M.IsGL] {r : M.World} {w : ℕ → M.World}

lemma forces_of_liftUp₁₂ (hrw : ∀ n, r ≺ w n) (hw : ∀ n, w (n + 1) ≺ w n)
    (hcof : ∀ y, r ≺ y → ∀ᶠ n in atTop, w n ≺ y) (d : ⊢ᴳ[𝐃] Γ.box ⟹[1] Δ.box) :
    r ⊩ (Γ.box ⟹ Δ.box) := by
  intro hΓ
  by_contra hΔ
  have h₁ : ∀ D ∈ Δ, ∀ᶠ n in atTop, w n ⊮ □D := by
    intro D hD
    have hrD : r ⊮ □D := fun hrD ↦ hΔ ⟨□D, FormulaFinset.mem_box.mpr ⟨D, hD, rfl⟩, hrD⟩
    obtain ⟨y, Rry, hy⟩ : ∃ y, r ≺ y ∧ y ⊮ D := by simpa using hrD
    exact (hcof y Rry).mono fun n Rny hn ↦ hy (hn y Rny)
  have h₂ : ∀ n, ∀ C ∈ Γ.box, w n ⊩ C := by
    intro n C hC
    obtain ⟨B, -, rfl⟩ := FormulaFinset.mem_box.mp hC
    exact fun y Rny ↦ hΓ _ hC y (IsTrans.trans _ _ _ (hrw n) Rny)
  obtain ⟨n, hn₁, hn₂⟩ :=
    ((eventually_forces M hw d rfl).and ((eventually_all_finset Δ).mpr h₁)).exists
  obtain ⟨E, hE, hnE⟩ := hn₁ (h₂ n)
  obtain ⟨D, hD, rfl⟩ := FormulaFinset.mem_box.mp hE
  exact hn₂ D hD hnE

/-- - [KKIM25, Theorem 5.8] -/
theorem forces_of_level₂ (hrw : ∀ n, r ≺ w n) (hw : ∀ n, w (n + 1) ≺ w n)
    (hcof : ∀ y, r ≺ y → ∀ᶠ n in atTop, w n ≺ y) {S : LayeredSequent α} (h : ⊢ᴳ[𝐃] S)
    (hS : S.level = 2) : r ⊩ S.toSequent := by
  induction h with
  | axm => exact fun h ↦ ⟨_, Finset.mem_singleton_self _, h _ (Finset.mem_singleton_self _)⟩
  | botL => exact fun h ↦ (h _ (Finset.mem_singleton_self _)).elim
  | wk _ hΓ hΔ ih => exact forcesSequent_wk (ih hS) hΓ hΔ
  | impL _ _ ih₁ ih₂ => exact forcesSequent_impL (ih₁ hS) (ih₂ hS)
  | impR _ ih => exact forcesSequent_impR (ih hS)
  | liftUp₁₂ d => exact forces_of_liftUp₁₂ M hrw hw hcof d
  | boxGL | boxL | liftUp₀₁ => nomatch hS

end

lemma truthlemma_bottom (hΛ : Λ.SubformulaClosed) {U : Sequent α} (hU : U.Saturated)
    (hUd : ⊬ᴳ[𝐃] U.ant ⟹[2] U.suc) {t : (logicGL.countermodel Λ).World}
    (hbox : ∀ {A}, □A ∈ t.ant → A ∈ t.ant)
    (ht : (U.ant.prebox.box ⟹ U.suc.prebox.box) ⊆ t.toSequent)
    {V : ℕ∞ → α → Prop} (hV : ∀ (n : ℕ) a, V n a ↔ #a ∈ t.ant) (hV' : ∀ a, V ⊤ a ↔ #a ∈ U.ant)
    (A : Formula α) :
    (A ∈ U.ant → Sum.inr ⊤ ⊩[(logicGL.countermodel Λ).attachTail t V] A) ∧
      (A ∈ U.suc → Sum.inr ⊤ ⊮[(logicGL.countermodel Λ).attachTail t V] A) := by
  have hchain := truthlemma_tail hΛ hbox hV
  induction A with
  | atom a =>
    constructor
    · exact (hV' a).mpr
    · exact fun h hf ↦ hUd (union ((hV' a).mp hf) h)
  | falsum => exact ⟨fun h ↦ (hUd (botL_mem h)).elim, fun _ ↦ not_forces_bot⟩
  | imp A B ihA ihB => grind
  | box A ih =>
    constructor
    · intro hA
      have hA' : □A ∈ t.ant :=
        ht.1 (FormulaFinset.mem_box.mpr ⟨A, FormulaFinset.mem_prebox.mpr hA, rfl⟩)
      rintro (y | j) Rxy
      · exact (hchain (□A) 0).1 hA' (.inl y) Rxy
      · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (attachTail.rel_inr_inr.mp Rxy))
        exact (hchain A m).1 (hbox hA')
    · intro hA hf
      have hA' : □A ∈ t.suc :=
        ht.2 (FormulaFinset.mem_box.mpr ⟨A, FormulaFinset.mem_prebox.mpr hA, rfl⟩)
      apply (hchain (□A) 0).2 hA'
      intro y Rxy
      exact hf y (IsTrans.trans _ _ _ (attachTail.rel_inr_inr.mpr (ENat.natCast_lt_top 0)) Rxy)

/-- - [KKIM25, Theorem 5.8] -/
theorem complete₂
    (hc : ∀ {κ : Type u} (M : Model κ α) [M.IsGL] (r : M.World) (w : ℕ → M.World),
      (∀ n, r ≺ w n) → (∀ n, w (n + 1) ≺ w n) → (∀ y, r ≺ y → ∀ᶠ n in atTop, w n ≺ y) →
      r ⊩ (Γ ⟹ Δ)) :
    ⊢ᴳ[𝐃] Γ ⟹[2] Δ := by
  by_contra hd
  have hΛ := Sequent.subformulaClosed_subfmls (S := Γ ⟹ Δ)
  obtain ⟨U, hU, hUΛ, hsat, hUd, -⟩ := exists_saturated hΛ Sequent.subset_subfmls hd
  have hsub : (U.ant.prebox.box ⟹ U.suc.prebox.box) ⊆ U := by
    constructor <;> intro C hC
    all_goals
      obtain ⟨B, hB, rfl⟩ := FormulaFinset.mem_box.mp hC
      exact FormulaFinset.mem_prebox.mp hB
  have hd₁ : ⊬ᴳ[𝐃] U.ant.prebox.box ⟹[1] U.suc.prebox.box := fun d ↦
    hUd ((liftUp₁₂ d).wk hsub.1 hsub.2)
  obtain ⟨t, ht, hbox⟩ :=
    exists_countermodel_world hΛ ⟨hsub.1.trans hUΛ.1, hsub.2.trans hUΛ.2⟩ hd₁
  let V : ℕ∞ → α → Prop := fun i a ↦ if i = ⊤ then #a ∈ U.ant else #a ∈ t.ant
  have key := truthlemma_bottom hΛ hsat hUd hbox ht (V := V) (by simp [V]) (by simp [V])
  have hcof : ∀ y, ((logicGL.countermodel (Γ ⟹ Δ).subfmls).attachTail t V).Rel (.inr ⊤) y →
      ∀ᶠ n : ℕ in atTop,
        ((logicGL.countermodel (Γ ⟹ Δ).subfmls).attachTail t V).Rel (.inr n) y := by
    rintro (y | j) Rxy
    · exact .of_forall fun _ ↦ Rxy
    · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (attachTail.rel_inr_inr.mp Rxy))
      exact eventually_atTop.mpr
        ⟨m + 1, fun n hn ↦ attachTail.rel_inr_inr.mpr (by exact_mod_cast hn)⟩
  have hr := hc ((logicGL.countermodel (Γ ⟹ Δ).subfmls).attachTail t V) (.inr ⊤) (fun n ↦ .inr n)
    (fun n ↦ attachTail.rel_inr_inr.mpr (ENat.natCast_lt_top n))
    (fun n ↦ attachTail.rel_inr_inr.mpr (by exact_mod_cast n.lt_succ_self)) hcof
  obtain ⟨D, hD, hrD⟩ := hr fun C hC ↦ (key C).1 (hU.1 hC)
  exact (key D).2 (hU.2 hD) hrD

/-- - [KKIM25, Theorems 4.1, 5.6, 5.8] -/
theorem cut (d₁ : ⊢ᴳ[𝐃] Γ₁ ⟹[ℓ] insert A Δ₁) (d₂ : ⊢ᴳ[𝐃] insert A Γ₂ ⟹[ℓ] Δ₂) :
    ⊢ᴳ[𝐃] Γ₁ ∪ Γ₂ ⟹[ℓ] Δ₁ ∪ Δ₂ := by
  match ℓ, d₁, d₂ with
  | 0, d₁, d₂ => exact iff_GL.mpr (logicGL.Derivable.cut (toGL d₁ rfl) (toGL d₂ rfl))
  | 1, d₁, d₂ =>
    exact complete₁ fun M _ w hw ↦ (((eventually_forces M hw d₁ rfl).and
      (eventually_forces M hw d₂ rfl)).mono fun _ hn ↦ forcesSequent_cut hn.1 hn.2).exists
  | 2, d₁, d₂ =>
    exact complete₂ fun M _ r w hrw hw hcof ↦ forcesSequent_cut
      (forces_of_level₂ M hrw hw hcof d₁ rfl) (forces_of_level₂ M hrw hw hcof d₂ rfl)

section Derived

variable {β : Type*} {Θ : FormulaFinset α}

lemma cut_singleton (d₁ : ⊢ᴳ[𝐃] Γ₁ ⟹[ℓ] {A}) (d₂ : ⊢ᴳ[𝐃] insert A Γ₂ ⟹[ℓ] Δ)
    (h : Γ₁ ∪ Γ₂ ⊆ Γ) : ⊢ᴳ[𝐃] Γ ⟹[ℓ] Δ :=
  (cut (Δ₁ := ∅) d₁ d₂).wk h (by grind)

lemma replace_ant {S : Finset β} {f g : β → Formula α}
    (h : ∀ x ∈ S, ⊢ᴳ[𝐃] {g x} ⟹[ℓ] {f x}) (d : ⊢ᴳ[𝐃] S.image f ∪ Θ ⟹[ℓ] Δ) :
    ⊢ᴳ[𝐃] S.image g ∪ Θ ⟹[ℓ] Δ := by
  classical
  induction S using Finset.induction_on generalizing Θ with
  | empty => simpa using d
  | insert x S hx ih =>
    have d₁ : ⊢ᴳ[𝐃] insert (f x) (S.image f ∪ Θ) ⟹[ℓ] Δ := d.wk (by grind) (by grind)
    have d₂ := cut_singleton (h x (by grind)) d₁ (Γ := S.image f ∪ insert (g x) Θ) (by grind)
    exact (ih (fun y hy ↦ h y (by grind)) d₂).wk (by grind) (by grind)

lemma unbox_of_persist (h : ∀ B ∈ Γ, ⊢ᴳ[𝐃] {B} ⟹[ℓ] {□B}) (d : ⊢ᴳ[𝐃] Γ.box ∪ Θ ⟹[ℓ] Δ) :
    ⊢ᴳ[𝐃] Γ ∪ Θ ⟹[ℓ] Δ :=
  (replace_ant (f := (□·)) (g := id) h d).wk (by grind) (by grind)

lemma box_of_persist (h : ∀ B ∈ Γ, ⊢ᴳ[𝐃] {B} ⟹[ℓ] {□B}) (d : ⊢ᴳ[𝐃] Γ.box ∪ Γ ⟹[0] {A}) :
    ⊢ᴳ[𝐃] Γ ⟹[ℓ] {□A} := by
  have d₁ : ⊢ᴳ[𝐃] Γ.box ∪ ∅ ⟹[ℓ] {□A} := (boxK4 d ℓ).wk (by grind) (by grind)
  exact (unbox_of_persist h d₁).wk (by grind) (by grind)

end Derived

end Modal.logicD.Derivable

end
