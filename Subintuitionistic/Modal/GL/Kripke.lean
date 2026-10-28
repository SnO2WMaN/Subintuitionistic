module

public import Subintuitionistic.Modal.GL.Basic
public import Subintuitionistic.Modal.Kripke
public import Mathlib.Basic.Finite.Prod

/-!
# Kripke soundness and completeness of `GL`

A sequent is derivable in the sequent calculus of `GL` if and only if it is valid in every
finite GL model. The finite countermodel of an unprovable sequent has the saturated
unprovable sequents inside a subformula-closed finite set as points.
-/

@[expose] public section

namespace Modal.GL.Gentzen

open Model Model.World

variable {κ α : Type*} [DecidableEq α] {M : Model κ α} [M.IsFiniteGL] {S : Sequent α}

/-- The modal rule is sound: Löb's principle on a finite irreflexive transitive frame. -/
lemma forces_box_of_löb {x : M.World} {Θ : FormulaFinset α} {A : Formula α}
    (hΘ : ∀ C ∈ Θ, x ⊩ □C) (ih : M ⊧ (insert (□A) (Θ ∪ Θ.image Formula.box) ⟹ {A})) :
    x ⊩ □A := by
  by_contra hx
  obtain ⟨y₀, hy₀⟩ : ∃ y, x ≺ y ∧ y ⊮ A := by simpa using hx
  obtain ⟨y, ⟨Rxy, hyA⟩, hmin⟩ := M.wellFounded_swap_rel.has_min {y | x ≺ y ∧ y ⊮ A} ⟨y₀, hy₀⟩
  have htr : ∀ z, y ≺ z → x ≺ z := fun z Ryz ↦ IsTrans.trans _ _ _ Rxy Ryz
  have hbox : y ⊩ □A := by
    by_contra hy
    grind
  have hall : ∀ C ∈ insert (□A) (Θ ∪ Θ.image Formula.box), y ⊩ C := by grind
  have := ih y
  grind

variable (M) in
/-- Every sequent derivable in `GL` holds at every point of every GL model.

- [SV82] -/
theorem sound (h : ⊢ᴳ[𝐆𝐋] S) : M ⊧ S := by
  intro x
  induction h generalizing x with
  | axm hA hB => grind
  | botL h => grind
  | impL hAB _ _ ih₁ ih₂ =>
    have := ih₁ x
    have := ih₂ x
    grind
  | impR hAB _ ih =>
    have := ih x
    grind
  | boxGL hΘ hA _ ih =>
    intro hall
    exact ⟨_, hA, forces_box_of_löb (fun C hC ↦ hall _ (hΘ (Finset.mem_image_of_mem _ hC))) ih⟩

end Modal.GL.Gentzen

namespace Modal.GL

open Model Model.World

variable {α : Type*} [DecidableEq α] {Λ : FormulaFinset α} {S T : Sequent α} {A : Formula α}

/-- The points of the countermodel: saturated unprovable sequents inside `Λ`. -/
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

/-- A maximal unprovable sequent inside a subformula-closed `Λ` is saturated. -/
lemma saturated_of_maximal (hΛ : Λ.SubformulaClosed) (hT : T ⊆ (Λ ⟹ Λ)) (hd : ⊬ᴳ[𝐆𝐋] T)
    (hmax : ∀ U, T ⊆ U → U ⊆ (Λ ⟹ Λ) → ⊬ᴳ[𝐆𝐋] U → U = T) : T.Saturated := by
  have key : ∀ U, T ⊆ U → U ⊆ (Λ ⟹ Λ) → U ⊆ T ∨ ⊢ᴳ[𝐆𝐋] U := by
    intro U h₁ h₂
    by_cases hU : ⊢ᴳ[𝐆𝐋] U
    · exact Or.inr hU
    · have e := hmax U h₁ h₂ hU
      exact Or.inl ⟨(congrArg Sequent.ant e).subset, (congrArg Sequent.suc e).subset⟩
  constructor
  · intro A B hAB
    have hAB' := hΛ.imp (hT.1 hAB)
    have h₁ := key (T.ant ⟹ insert A T.suc) (by grind) (by grind)
    have h₂ := key (insert B T.ant ⟹ T.suc) (by grind) (by grind)
    by_contra hc
    have d₁ : ⊢ᴳ[𝐆𝐋] T.ant ⟹ insert A T.suc := by grind
    have d₂ : ⊢ᴳ[𝐆𝐋] insert B T.ant ⟹ T.suc := by grind
    exact hd (.impL hAB d₁ d₂)
  · intro A B hAB
    have hAB' := hΛ.imp (hT.2 hAB)
    have h := key (insert A T.ant ⟹ insert B T.suc) (by grind) (by grind)
    obtain h | d := h
    · grind
    · exact (hd (.impR hAB d)).elim

/-- An unprovable sequent inside a subformula-closed `Λ` extends to a point of the countermodel. -/
lemma lindenbaum (hΛ : Λ.SubformulaClosed) (hS : S ⊆ (Λ ⟹ Λ)) (h : ⊬ᴳ[𝐆𝐋] S) :
    ∃ x : SaturatedSequent Λ, S ⊆ x.toSequent := by
  obtain ⟨T, h₁, h₂, h₃, hmax⟩ := Sequent.exists_maximal Gentzen hS h
  exact ⟨⟨T, saturated_of_maximal hΛ h₂ h₃ hmax, h₂, h₃⟩, h₁⟩

end SaturatedSequent

open SaturatedSequent

/-- The finite countermodel. `x ≺ y` when every `□A` in the antecedent of `x` is in that of `y`
together with `A`, and the antecedent of `y` has a boxed formula that of `x` lacks. -/
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

/-- If `□A` is in the succedent of `x`, some `y` with `x ≺ y` has `A` in its succedent. -/
lemma exists_rel_of_box_mem_suc (hΛ : Λ.SubformulaClosed) {x : (countermodel Λ).World}
    (h : □A ∈ x.suc) : ∃ y : (countermodel Λ).World, x ≺ y ∧ A ∈ y.suc := by
  let Θ : FormulaFinset α := Λ.filter (fun C ↦ □C ∈ x.ant)
  have hΘ : ∀ {C}, C ∈ Θ ↔ C ∈ Λ ∧ □C ∈ x.ant := by simp [Θ]
  have hboxΛ : □A ∈ Λ := x.subset.2 h
  have := x.subset
  have hU : (insert (□A) (Θ ∪ Θ.image Formula.box) ⟹ {A}) ⊆ (Λ ⟹ Λ) := by
    have := hΛ.box hboxΛ
    constructor <;> grind
  have hnd : ⊬ᴳ[𝐆𝐋] (insert (□A) (Θ ∪ Θ.image Formula.box) ⟹ {A}) := by
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

namespace Gentzen

universe u

variable {α : Type u} [DecidableEq α] {S : Sequent α}

/-- A sequent that holds in every finite GL model is derivable in `GL`.

- [Seg71]
- [SV82] -/
theorem complete (h : ∀ {κ : Type u} (M : Model κ α), [M.IsFiniteGL] → M ⊧ S) : ⊢ᴳ[𝐆𝐋] S := by
  by_contra hS
  obtain ⟨x, hx⟩ := lindenbaum Sequent.subformulaClosed_subfmls Sequent.subset_subfmls hS
  obtain ⟨D, hD, hxD⟩ := h (countermodel S.subfmls) x
    fun C hC ↦ (countermodel.truthlemma Sequent.subformulaClosed_subfmls x).1 (hx.1 hC)
  exact (countermodel.truthlemma Sequent.subformulaClosed_subfmls x).2 (hx.2 hD) hxD

/-- Completeness and soundness of `GL`: a sequent is derivable iff it holds in every finite GL
model.

- [Seg71]
- [SV82] -/
theorem iff_valid : ⊢ᴳ[𝐆𝐋] S ↔ ∀ {κ : Type u} (M : Model κ α), [M.IsFiniteGL] → M ⊧ S :=
  ⟨fun h _ M _ ↦ sound M h, complete⟩

end Gentzen

end Modal.GL

end
