module

public import Subintuitionistic.Propositional.DPL.Basic
public import Subintuitionistic.Propositional.FPL.Kripke
public import Subintuitionistic.Propositional.Kripke.Extension
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Tactic.TFAE

/-!
# Kripke semantics for `𝐃𝐏𝐋`
-/

@[expose] public section

namespace Propositional.logicDPL.Derivable

open Model Model.World Filter
open FormulaFinset (imps)

universe u

variable {α : Type u} [DecidableEq α] {ℓ : Fin 3} {Γ Δ Ξ : FormulaFinset α} {S S₁ : Sequent α}
  {κ : Type*} {M : Model κ α} {r t : M.World} {s : M.InfiniteDescendingChain} {V : α → Prop}
  {A B : Formula α}

/-! ### Saturation -/

lemma exists_saturated (hΛ : Ξ.SubformulaClosed) (hS : S ⊆ (Ξ ⟹ Ξ))
    (hd : ⊬ᴳ[𝐃𝐏𝐋] S.ant ⟹[ℓ] S.suc) :
    ∃ U, S ⊆ U ∧ U ⊆ (Ξ ⟹ Ξ) ∧ U.Saturated ∧ (⊬ᴳ[𝐃𝐏𝐋] U.ant ⟹[ℓ] U.suc) ∧
      (ℓ = 1 → ∀ {A B}, A 🡒 B ∈ U.ant → A ∈ U.suc ∨ B ∈ U.ant) := by
  obtain ⟨U, h₁, h₂, h₃, hmax⟩ :=
    Sequent.exists_maximal (fun U ↦ ⊢ᴳ[𝐃𝐏𝐋] U.ant ⟹[ℓ] U.suc) hS hd
  have hsat := Sequent.saturated_of_maximal (fun U ↦ ⊢ᴳ[𝐃𝐏𝐋] U.ant ⟹[ℓ] U.suc) hΛ h₂ h₃ hmax
    andL_of_mem andR_of_mem orL_of_mem orR_of_mem
  have himp : ℓ = 1 → ∀ {A B}, A 🡒 B ∈ U.ant → A ∈ U.suc ∨ B ∈ U.ant := by
    rintro rfl A B hAB
    have := hΛ.imp (h₂.1 hAB)
    by_contra hc
    have d₁ : ⊢ᴳ[𝐃𝐏𝐋] U.ant ⟹[1] insert A U.suc := by
      by_contra d
      have e := hmax (U.ant ⟹ insert A U.suc) (by grind) (by grind) d
      exact hc (.inl ((congrArg Sequent.suc e).subset (Finset.mem_insert_self _ _)))
    have d₂ : ⊢ᴳ[𝐃𝐏𝐋] insert B U.ant ⟹[1] U.suc := by
      by_contra d
      have e := hmax (insert B U.ant ⟹ U.suc) (by grind) (by grind) d
      exact hc (.inr ((congrArg Sequent.ant e).subset (Finset.mem_insert_self _ _)))
    exact h₃ (impL_of_mem hAB d₁ d₂)
  exact ⟨U, h₁, h₂, hsat, h₃, himp⟩

lemma exists_countermodel_world (hΛ : Ξ.SubformulaClosed) (hU : S ⊆ (Ξ ⟹ Ξ))
    (hd : ⊬ᴳ[𝐃𝐏𝐋] S.ant ⟹[1] S.suc) :
    ∃ t : (logicFPL.countermodel Ξ).World, (∀ C ∈ S.ant, t ⊩ C) ∧ (∀ D ∈ S.suc, t ⊮ D) := by
  obtain ⟨t, ht⟩ := logicFPL.SaturatedSequent.lindenbaum hΛ hU fun d ↦ hd (ofFPL d).liftUp₀₁
  exact ⟨t, fun C hC ↦ (logicFPL.countermodel.truthlemma hΛ t).1 (ht.1 hC),
    fun D hD ↦ (logicFPL.countermodel.truthlemma hΛ t).2 (ht.2 hD)⟩

/-! ### The level `1` -/

omit [DecidableEq α] in
variable (s) in
lemma eventually_forces_imp [IsTrans _ M.Rel] (A B : Formula α) :
    ∀ᶠ n in atTop, s n ⊩ A 🡒 B → s n ⊩ A → s n ⊩ B := by
  by_cases h : ∀ n, s n ⊩ A 🡒 B
  · exact .of_forall fun n _ hA ↦ h (n + 1) (s n) (s.rel_succ n) hA
  · obtain ⟨m, hm⟩ := not_forall.mp h
    refine eventually_atTop.mpr ⟨m + 1, fun n hn hn' ↦ absurd (forces_of_rel ?_ hn') hm⟩
    exact Nat.rel_of_forall_rel_succ_of_lt (Function.swap M.Rel) s.rel_succ hn

variable (M) in
theorem eventually_forces [M.IsFPL] {S : LayeredSequent α}
    (h : ⊢ᴳ[𝐃𝐏𝐋] S) (hS : S.level = 1) : ∀ᶠ n in atTop, s n ⊩ S.toSequent := by
  induction h with
  | axm => exact .of_forall fun _ h ↦ ⟨_, Finset.mem_singleton_self _, h _ (by simp)⟩
  | botL => exact .of_forall fun _ h ↦ (h _ (Finset.mem_singleton_self _)).elim
  | wk _ hΓ hΔ ih => exact (ih hS).mono fun _ hn ↦ forcesSequent_wk hn hΓ hΔ
  | andL _ ih => exact (ih hS).mono fun _ hn ↦ forcesSequent_andL hn
  | andR _ _ ih₁ ih₂ => exact ((ih₁ hS).and (ih₂ hS)).mono fun _ hn ↦ forcesSequent_andR hn.1 hn.2
  | orL _ _ ih₁ ih₂ => exact ((ih₁ hS).and (ih₂ hS)).mono fun _ hn ↦ forcesSequent_orL hn.1 hn.2
  | orR _ ih => exact (ih hS).mono fun _ hn ↦ forcesSequent_orR hn
  | @impL _ _ A B _ _ ih₁ ih₂ =>
    exact (((ih₁ hS).and (ih₂ hS)).and (eventually_forces_imp s A B)).mono fun _ hn ↦ by
      grind [ForcesSequent]
  | liftUp₀₁ d => exact .of_forall fun n ↦ logicFPL.Derivable.sound M (toFPL d rfl) (s n)
  | impR | liftUp₁₂ => nomatch hS

omit [DecidableEq α] in
lemma truthlemma_tail (hU : S.Saturated)
    (himp : ∀ {A B}, A 🡒 B ∈ S.ant → A ∈ S.suc ∨ B ∈ S.ant)
    (ht₁ : ∀ C ∈ S.ant, t ⊩ C) (ht₂ : ∀ D ∈ S.suc, t ⊮ D) (A : Formula α) (n : ℕ) :
    (A ∈ S.ant → Sum.inr (n : ℕ∞) ⊩[M.ωExtension t V] A) ∧
      (A ∈ S.suc → Sum.inr (n : ℕ∞) ⊮[M.ωExtension t V] A) := by
  induction A generalizing n with
  | atom a =>
    constructor;
    · intro ha;
      constructor;
      · exact ht₁ _ ha;
      · tauto;
    · rintro ha ⟨hn, _⟩;
      exact ht₂ _ ha hn;
  | falsum => exact ⟨fun h ↦ (ht₁ ⊥ h).elim, fun _ ↦ not_forces_bot⟩
  | and A B ihA ihB =>
    obtain ⟨h₁, h₂, -, -⟩ := hU;
    grind
  | or A B ihA ihB =>
    obtain ⟨-, -, h₁, h₂⟩ := hU;
    grind
  | imp A B ihA ihB =>
    constructor
    · rintro hAB (y | j) Rny hA
      · rcases ωExtension.rel_inr_inl.mp Rny with rfl | Rty
        · rcases himp hAB with hA' | hB'
          · exact absurd (ωExtension.forces_inl.mp hA) (ht₂ _ hA')
          · exact ωExtension.forces_inl.mpr (ht₁ _ hB')
        · exact ωExtension.forces_inl.mpr (ht₁ _ hAB y Rty (ωExtension.forces_inl.mp hA))
      · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt (ωExtension.rel_inr_inr.mp Rny))
        rcases himp hAB with hA' | hB'
        · exact absurd hA ((ihA m).2 hA')
        · exact (ihB m).1 hB'
    · intro hAB hn
      obtain ⟨y, Rty, hy₁, hy₂⟩ : ∃ y, t ≺ y ∧ y ⊩ A ∧ y ⊮ B := by grind
      exact hy₂ (ωExtension.forces_inl.mp
        (hn (.inl y) (ωExtension.rel_inr_inl.mpr (.inr Rty)) (ωExtension.forces_inl.mpr hy₁)))

theorem complete₁
    (hc : ∀ {κ : Type u} (M : Model κ α) [M.IsFiniteFPL] (t : M.World) (V : α → Prop),
      ∃ n : ℕ, Sum.inr (n : ℕ∞) ⊩[M.ωExtension t V] (Γ ⟹ Δ)) :
    ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[1] Δ := by
  by_contra hd
  have hΛ := Sequent.subformulaClosed_subfmls (S := Γ ⟹ Δ)
  obtain ⟨U, hU, hUΛ, hsat, hUd, himp⟩ := exists_saturated hΛ Sequent.subset_subfmls hd
  obtain ⟨t, ht₁, ht₂⟩ := exists_countermodel_world hΛ hUΛ hUd
  have key := truthlemma_tail (V := fun _ ↦ True) hsat (himp rfl) ht₁ ht₂
  obtain ⟨n, hn⟩ := hc (logicFPL.countermodel (Γ ⟹ Δ).subfmls) t fun _ ↦ True
  obtain ⟨D, hD, hnD⟩ := hn fun C hC ↦ (key C n).1 (hU.1 hC)
  exact (key D n).2 (hU.2 hD) hnD

/-! ### The level `2` -/

variable (M) in
lemma forces_of_liftUp₁₂ [M.IsFPL] (hsr : s.ConvergesTo r)
    {P Q : Finset (Formula α × Formula α)} {Φ : Finset α}
    (d : ⊢ᴳ[𝐃𝐏𝐋] imps P ∪ Φ.image (#·) ⟹[1] imps Q) :
    r ⊩ (imps P ∪ Φ.image (#·) ⟹ imps Q) := by
  intro hΓ
  by_contra hΔ
  have h₁ : ∀ p ∈ Q, ∀ᶠ n in atTop, s n ⊮ p.1 🡒 p.2 := by
    intro p hp
    have hr : r ⊮ p.1 🡒 p.2 := fun h ↦ hΔ ⟨_, FormulaFinset.mem_imps_of_mem hp, h⟩
    obtain ⟨y, Rry, hy₁, hy₂⟩ : ∃ y, r ≺ y ∧ y ⊩ p.1 ∧ y ⊮ p.2 := by grind
    exact (hsr.eventually_rel y Rry).mono fun n Rny hn ↦ hy₂ (hn y Rny hy₁)
  obtain ⟨n, hn₁, hn₂⟩ :=
    ((eventually_forces M d rfl).and ((eventually_all_finset Q).mpr h₁)).exists
  obtain ⟨E, hE, hnE⟩ := hn₁ fun C hC ↦ forces_of_rel (hsr.rel n) (hΓ C hC)
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hE
  exact hn₂ p hp hnE

variable (M) in
theorem forces_of_level₂ [M.IsFPL] (hsr : s.ConvergesTo r)
    {S : LayeredSequent α} (h : ⊢ᴳ[𝐃𝐏𝐋] S) (hS : S.level = 2) : r ⊩ S.toSequent := by
  induction h with
  | axm => exact fun h ↦ ⟨_, Finset.mem_singleton_self _, h _ (Finset.mem_singleton_self _)⟩
  | botL => exact fun h ↦ (h _ (Finset.mem_singleton_self _)).elim
  | wk _ hΓ hΔ ih => exact forcesSequent_wk (ih hS) hΓ hΔ
  | andL _ ih => exact forcesSequent_andL (ih hS)
  | andR _ _ ih₁ ih₂ => exact forcesSequent_andR (ih₁ hS) (ih₂ hS)
  | orL _ _ ih₁ ih₂ => exact forcesSequent_orL (ih₁ hS) (ih₂ hS)
  | orR _ ih => exact forcesSequent_orR (ih hS)
  | liftUp₁₂ d => exact forces_of_liftUp₁₂ M hsr d
  | impL | impR | liftUp₀₁ => nomatch hS

lemma truthlemma_bottom [M.IsFPL] (hU : S.Saturated) (hUd : ⊬ᴳ[𝐃𝐏𝐋] S.ant ⟹[2] S.suc)
    (hU₁ : ∀ {A}, A ∈ S.ant → (∃ a, A = #a) ∨ (∃ B C, A = B 🡒 C) → A ∈ S₁.ant)
    (hU₁' : ∀ {B C}, B 🡒 C ∈ S.suc → B 🡒 C ∈ S₁.suc)
    (htail : ∀ A (n : ℕ), (A ∈ S₁.ant → Sum.inr (n : ℕ∞) ⊩[M.ωExtension t V] A) ∧
      (A ∈ S₁.suc → Sum.inr (n : ℕ∞) ⊮[M.ωExtension t V] A))
    (hV : ∀ a, V a ↔ #a ∈ S.ant) (A : Formula α) :
    (A ∈ S.ant → Sum.inr ⊤ ⊩[M.ωExtension t V] A) ∧
      (A ∈ S.suc → Sum.inr ⊤ ⊮[M.ωExtension t V] A) := by
  induction A with
  | atom a =>
    constructor
    · intro ha
      exact ⟨((htail (#a) 0).1 (hU₁ ha (.inl ⟨a, rfl⟩))).1, fun _ ↦ (hV a).mpr ha⟩
    · exact fun h hf ↦ hUd (axm_mem ((hV a).mp (hf.2 rfl)) h ⟨a, rfl⟩)
  | falsum => exact ⟨fun h ↦ (hUd (botL_mem h)).elim, fun _ ↦ not_forces_bot⟩
  | and A B ihA ihB =>
    obtain ⟨h₁, h₂, -, -⟩ := hU
    grind
  | or A B ihA ihB =>
    obtain ⟨-, -, h₁, h₂⟩ := hU
    grind
  | imp A B =>
    constructor
    · intro hAB y Rty
      obtain ⟨n, Rny⟩ : ∃ n : ℕ, (M.ωExtension t V).Rel (.inr n) y := by
        rcases y with y | j
        · exact ⟨0, Rty⟩
        · obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt Rty)
          exact ⟨m + 1, ωExtension.rel_inr_succ m⟩
      exact (htail (A 🡒 B) n).1 (hU₁ hAB (.inr ⟨A, B, rfl⟩)) y Rny
    · intro hAB hf
      exact (htail (A 🡒 B) 0).2 (hU₁' hAB)
        (forces_of_rel (ωExtension.rel_inr_inr.mpr (ENat.natCast_lt_top 0)) hf)

theorem complete₂
    (hc : ∀ {κ : Type u} (M : Model κ α) [M.IsFiniteFPL] (t : M.World) (V : α → Prop),
      .inr ⊤ ⊩[M.ωExtension t V] (Γ ⟹ Δ)) :
    ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[2] Δ := by
  by_contra hd
  have hΛ := Sequent.subformulaClosed_subfmls (S := Γ ⟹ Δ)
  obtain ⟨U, hU, hUΛ, hsat, hUd, -⟩ := exists_saturated hΛ Sequent.subset_subfmls hd
  obtain ⟨P, hP₁, hP₂⟩ := FormulaFinset.exists_imps U.ant
  obtain ⟨Q, hQ₁, hQ₂⟩ := FormulaFinset.exists_imps U.suc
  have hinj : Function.Injective (Formula.atom : α → Formula α) := fun _ _ h ↦ Formula.atom.inj h
  set Φ := U.ant.preimage (#·) hinj.injOn
  have hΦ : Φ.image (#·) ⊆ U.ant := fun A hA ↦ by grind [Finset.mem_preimage]
  have hd₁ : ⊬ᴳ[𝐃𝐏𝐋] imps P ∪ Φ.image (#·) ⟹[1] imps Q := fun d ↦
    hUd (d.liftUp₁₂.wk (Finset.union_subset hP₁ hΦ) hQ₁)
  obtain ⟨U₁, hU₁, hU₁Λ, hsat₁, hU₁d, himp₁⟩ :=
    exists_saturated (S := imps P ∪ Φ.image (#·) ⟹ imps Q) hΛ
      ⟨(Finset.union_subset hP₁ hΦ).trans hUΛ.1, hQ₁.trans hUΛ.2⟩ hd₁
  obtain ⟨t, ht₁, ht₂⟩ := exists_countermodel_world hΛ hU₁Λ hU₁d
  have htail := truthlemma_tail (V := fun a ↦ #a ∈ U.ant) hsat₁ (himp₁ rfl) ht₁ ht₂
  have key := truthlemma_bottom hsat hUd
    (fun hA h ↦ hU₁.1 (by grind [Finset.mem_preimage, FormulaFinset.imps]))
    (fun h ↦ hU₁.2 (by grind [FormulaFinset.imps])) htail fun _ ↦ Iff.rfl
  have hr := hc (logicFPL.countermodel (Γ ⟹ Δ).subfmls) t fun a ↦ #a ∈ U.ant
  obtain ⟨D, hD, hrD⟩ := hr fun C hC ↦ (key C).1 (hU.1 hC)
  exact (key D).2 (hU.2 hD) hrD

/-! ### Characterizations -/

theorem level₀_TFAE : [
    ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[0] Δ,
    ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ,
    ∀ {κ : Type u} (M : Model κ α), [M.IsFPL] → M ⊧ Γ ⟹ Δ,
    ∀ {κ : Type u} (M : Model κ α), [M.IsFiniteFPL] → M ⊧ Γ ⟹ Δ
  ].TFAE := by
  tfae_have 1 ↔ 2 := iff_FPL
  tfae_have 2 → 3 := fun d _ M _ ↦ logicFPL.Derivable.sound M d
  tfae_have 3 → 4 := fun h _ M _ ↦ h M
  tfae_have 4 → 2 := logicFPL.Derivable.complete
  tfae_finish

theorem level₁_TFAE : [
    ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[1] Δ,
    ∀ {κ : Type u} (M : Model κ α) [M.IsFPL] (s : M.InfiniteDescendingChain),
      ∀ᶠ n in atTop, s n ⊩ (Γ ⟹ Δ),
    ∀ {κ : Type u} (M : Model κ α) [M.IsFPL] (s : M.InfiniteDescendingChain),
      ∃ n, s n ⊩ (Γ ⟹ Δ),
    ∀ {κ : Type u} (M : Model κ α) [M.IsFPL] (t : M.World) (V : α → Prop),
      ∃ n : ℕ, Sum.inr (n : ℕ∞) ⊩[M.ωExtension t V] (Γ ⟹ Δ),
    ∀ {κ : Type u} (M : Model κ α) [M.IsFiniteFPL] (t : M.World) (V : α → Prop),
      ∃ n : ℕ, Sum.inr (n : ℕ∞) ⊩[M.ωExtension t V] (Γ ⟹ Δ)
  ].TFAE := by
  tfae_have 1 → 2 := fun d _ M _ s ↦ eventually_forces M d rfl
  tfae_have 2 → 3 := fun h _ M _ s ↦ (h M s).exists
  tfae_have 3 → 4 := fun h _ M _ t V ↦ h (M.ωExtension t V) (ωExtension.chain M t V)
  tfae_have 4 → 5 := fun h _ M _ t V ↦ h M t V
  tfae_have 5 → 1 := complete₁
  tfae_finish

theorem level₂_TFAE : [
    ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[2] Δ,
    ∀ {κ : Type u} (M : Model κ α) [M.IsFPL] (s : M.InfiniteDescendingChain) (r : M.World),
      s.ConvergesTo r → r ⊩ (Γ ⟹ Δ),
    ∀ {κ : Type u} (M : Model κ α) [M.IsFPL] (t : M.World) (V : α → Prop),
      Sum.inr ⊤ ⊩[M.ωExtension t V] (Γ ⟹ Δ),
    ∀ {κ : Type u} (M : Model κ α) [M.IsFiniteFPL] (t : M.World) (V : α → Prop),
      Sum.inr ⊤ ⊩[M.ωExtension t V] (Γ ⟹ Δ)
  ].TFAE := by
  tfae_have 1 → 2 := fun d _ M _ s r hsr ↦ forces_of_level₂ M hsr d rfl
  tfae_have 2 → 3 := fun h _ M _ t V ↦
    h (M.ωExtension t V) (ωExtension.chain M t V) (.inr ⊤) ωExtension.convergesTo_top
  tfae_have 3 → 4 := fun h _ M _ t V ↦ h M t V
  tfae_have 4 → 1 := complete₂
  tfae_finish

end Propositional.logicDPL.Derivable

end
