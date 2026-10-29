module

public import Subintuitionistic.Modal.GL.Basic
public import Subintuitionistic.Modal.Kripke
public import Mathlib.Basic.Finite.Prod

/-!
# Kripke soundness and completeness of `GL`

`⊢ᴳ[𝐆𝐋] S ↔ ∀ M, [M.IsFiniteGL] → M ⊧ S` (`logicGL.Derivable.iff_valid`). The countermodel of an
unprovable sequent is `countermodel`, whose points are `SaturatedSequent`s.
-/

@[expose] public section

namespace Modal.logicGL.Derivable

open Model Model.World

variable {κ α : Type*} [DecidableEq α] {M : Model κ α} [M.IsGL] {S : Sequent α}

/-- The modal rule is sound: Löb's principle on a transitive conversely well-founded frame. -/
lemma forces_box_of_löb {x : M.World} {Θ : FormulaFinset α} {A : Formula α}
    (hΘ : ∀ C ∈ Θ, x ⊩ □C) (ih : M ⊧ (insert (□A) (Θ ∪ Θ.box) ⟹ {A})) :
    x ⊩ □A := by
  by_contra hx
  obtain ⟨y₀, hy₀⟩ : ∃ y, x ≺ y ∧ y ⊮ A := by simpa using hx
  obtain ⟨y, ⟨Rxy, hyA⟩, hmin⟩ := IsGL.converseWellFounded.has_min {y | x ≺ y ∧ y ⊮ A} ⟨y₀, hy₀⟩
  have htr : ∀ z, y ≺ z → x ≺ z := fun z Ryz ↦ IsTrans.trans _ _ _ Rxy Ryz
  have hbox : y ⊩ □A := by
    by_contra hy
    grind
  have hall : ∀ C ∈ insert (□A) (Θ ∪ Θ.box), y ⊩ C := by grind
  have := ih y
  grind

variable (M) in
/-- - [SV82] -/
theorem sound (h : ⊢ᴳ[𝐆𝐋] S) : M ⊧ S := by
  induction h with
  | axm hA hB => grind
  | botL h => grind
  | impL hAB _ _ ih₁ ih₂ => exact fun x ↦ by grind [ih₁ x, ih₂ x]
  | impR hAB _ ih => exact fun x ↦ by grind [ih x]
  | boxGL hΘ hA _ ih => exact fun x hx ↦ ⟨_, hA, forces_box_of_löb (by grind) ih⟩

end Modal.logicGL.Derivable

namespace Modal.logicGL

open Model Model.World

variable {α : Type*} [DecidableEq α] {Λ : FormulaFinset α} {S T : Sequent α} {A : Formula α}

/-- The points of the countermodel. -/
structure SaturatedSequent (Λ : FormulaFinset α) extends Sequent α where
  saturated : toSequent.Saturated
  subset : toSequent ⊆ (Λ ⟹ Λ)
  unprovable : ⊬ᴳ[𝐆𝐋] toSequent

namespace SaturatedSequent

@[ext] lemma ext {x y : SaturatedSequent Λ} (ha : x.ant = y.ant) (hs : x.suc = y.suc) : x = y := by
  obtain ⟨⟨_, _⟩, _⟩ := x
  obtain ⟨⟨_, _⟩, _⟩ := y
  simp_all

instance : Finite (SaturatedSequent Λ) :=
  Finite.of_injective
    (fun x ↦ ((⟨x.ant, Finset.mem_powerset.mpr x.subset.1⟩ : Λ.powerset),
      (⟨x.suc, Finset.mem_powerset.mpr x.subset.2⟩ : Λ.powerset)))
    fun x y h ↦ by
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
      exact ext (congrArg Subtype.val h₁) (congrArg Subtype.val h₂)

lemma lindenbaum (hΛ : Λ.SubformulaClosed) (hS : S ⊆ (Λ ⟹ Λ)) (h : ⊬ᴳ[𝐆𝐋] S) :
    ∃ x : SaturatedSequent Λ, S ⊆ x.toSequent := by
  obtain ⟨T, h₁, h₂, h₃, hmax⟩ := Sequent.exists_maximal Derivable hS h
  exact ⟨⟨T, Sequent.saturated_of_maximal Derivable hΛ h₂ h₃ hmax (fun hAB d₁ d₂ ↦ .impL hAB d₁ d₂)
    (fun hAB d ↦ .impR hAB d), h₂, h₃⟩, h₁⟩

end SaturatedSequent

open SaturatedSequent

def countermodel (Λ : FormulaFinset α) : Model (SaturatedSequent Λ) α where
  Rel' x y := (∀ A, □A ∈ x.ant → A ∈ y.ant ∧ □A ∈ y.ant) ∧ ∃ A, □A ∈ y.ant ∧ □A ∉ x.ant
  Val' x a := #a ∈ x.ant

namespace countermodel

instance : (countermodel Λ).IsFiniteGL where
  trans _ _ _ Rxy Ryz := by
    obtain ⟨B, hB, hBx⟩ := Rxy.2
    exact ⟨fun A hA ↦ Ryz.1 A (Rxy.1 A hA).2, B, (Ryz.1 B hB).2, hBx⟩
  irrefl _ Rxx := by
    obtain ⟨A, hA, hAx⟩ := Rxx.2
    exact hAx hA

lemma exists_rel_of_box_mem_suc (hΛ : Λ.SubformulaClosed) {x : (countermodel Λ).World}
    (h : □A ∈ x.suc) : ∃ y : (countermodel Λ).World, x ≺ y ∧ A ∈ y.suc := by
  let Θ : FormulaFinset α := Λ.filter (fun C ↦ □C ∈ x.ant)
  have hΘ : ∀ {C}, C ∈ Θ ↔ C ∈ Λ ∧ □C ∈ x.ant := by simp [Θ]
  have hboxΛ : □A ∈ Λ := x.subset.2 h
  have := x.subset
  have hU : (insert (□A) (Θ ∪ Θ.box) ⟹ {A}) ⊆ (Λ ⟹ Λ) := by
    have := hΛ.box hboxΛ
    constructor <;> grind
  have hnd : ⊬ᴳ[𝐆𝐋] (insert (□A) (Θ ∪ Θ.box) ⟹ {A}) := by
    intro hd
    apply x.unprovable (.boxGL (Θ := Θ) _ h hd)
    grind
  obtain ⟨y, hy⟩ := lindenbaum hΛ hU hnd
  have hΘy : ∀ C ∈ Θ, C ∈ y.ant ∧ □C ∈ y.ant := by grind
  have hx : □A ∉ x.ant := fun hA ↦ x.unprovable (.axm hA h)
  exact ⟨y, ⟨fun C hC ↦ hΘy C (hΘ.mpr ⟨hΛ.box (x.subset.1 hC), hC⟩), A, hy.1 (by simp), hx⟩,
    hy.2 (by simp)⟩

lemma truthlemma (hΛ : Λ.SubformulaClosed) (x : (countermodel Λ).World) :
    (A ∈ x.ant → x ⊩ A) ∧ (A ∈ x.suc → x ⊮ A) := by
  induction A generalizing x with
  | atom a =>
    constructor
    · exact id
    · intro h hx
      exact x.unprovable (.axm hx h)
  | falsum =>
    constructor
    · intro h
      exact (x.unprovable (.botL h)).elim
    · exact fun _ ↦ not_forces_bot
  | imp A B ihA ihB =>
    have := x.saturated
    have := ihA x
    have := ihB x
    grind
  | box A ih =>
    constructor
    · intro h y Rxy
      exact (ih y).1 (Rxy.1 A h).1
    · intro h
      by_contra hx
      obtain ⟨y, Rxy, hy⟩ := exists_rel_of_box_mem_suc hΛ h
      exact (ih y).2 hy (hx y Rxy)

end countermodel

namespace Derivable

universe u

variable {α : Type u} [DecidableEq α] {S : Sequent α}

/-- - [Seg71]
- [SV82] -/
theorem complete (h : ∀ {κ : Type u} (M : Model κ α), [M.IsFiniteGL] → M ⊧ S) : ⊢ᴳ[𝐆𝐋] S := by
  by_contra hS
  obtain ⟨x, hx⟩ := lindenbaum Sequent.subformulaClosed_subfmls Sequent.subset_subfmls hS
  obtain ⟨D, hD, hxD⟩ := h (countermodel S.subfmls) x
    fun C hC ↦ (countermodel.truthlemma Sequent.subformulaClosed_subfmls x).1 (hx.1 hC)
  exact (countermodel.truthlemma Sequent.subformulaClosed_subfmls x).2 (hx.2 hD) hxD

/-- - [Seg71]
- [SV82] -/
theorem iff_valid : ⊢ᴳ[𝐆𝐋] S ↔ ∀ {κ : Type u} (M : Model κ α), [M.IsFiniteGL] → M ⊧ S :=
  ⟨fun h _ M _ ↦ sound M h, complete⟩

variable {Γ Γ' Γ₁ Γ₂ Δ Δ' Δ₁ Δ₂ : FormulaFinset α} {A : Formula α}

lemma wk (d : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐆𝐋] Γ' ⟹ Δ' := by
  apply complete
  intro _ M _ x hx
  obtain ⟨D, hD, hxD⟩ := sound M d x fun C hC ↦ hx C (hΓ hC)
  exact ⟨D, hΔ hD, hxD⟩

/-- - [SV82] -/
theorem cut (d₁ : ⊢ᴳ[𝐆𝐋] Γ₁ ⟹ insert A Δ₁) (d₂ : ⊢ᴳ[𝐆𝐋] insert A Γ₂ ⟹ Δ₂) :
    ⊢ᴳ[𝐆𝐋] Γ₁ ∪ Γ₂ ⟹ Δ₁ ∪ Δ₂ :=
  complete fun M _ x ↦ forcesSequent_cut (sound M d₁ x) (sound M d₂ x)

end Derivable

end Modal.logicGL

end
