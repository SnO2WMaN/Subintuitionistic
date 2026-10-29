module

public import Subintuitionistic.Modal.Sequent

/-!
# The sequent calculus of `D`

`logicD.Derivation` is a cut-free calculus on layered sequents with levels `0`, `1`, `2`; the
levels `0` and `1` alone are the calculus of `S`. `𝐒` and `𝐃` are given by derivability at level
`1` and `2`. `erase_bot`, `invImpR`, `invImpL_left`, `invImpL_right` and `invImps` do not
increase the height.
-/

@[expose] public section

namespace Modal

namespace logicD

variable {α : Type*} [DecidableEq α]

/-- - [Nog26, Definitions 3.1, 6.1] -/
inductive Derivation : LayeredSequent α → Type _
  | axm (ℓ) (a : α) : Derivation ({#a} ⟹[ℓ] {#a})
  | botL (ℓ) : Derivation ({⊥} ⟹[ℓ] ∅)
  | wk {ℓ Γ Γ' Δ Δ'} :
    Derivation (Γ ⟹[ℓ] Δ) → Γ ⊆ Γ' → Δ ⊆ Δ' → Derivation (Γ' ⟹[ℓ] Δ')
  | impL {ℓ Γ Δ A B} :
    Derivation (Γ ⟹[ℓ] insert A Δ) → Derivation (insert B Γ ⟹[ℓ] Δ) →
      Derivation (insert (A 🡒 B) Γ ⟹[ℓ] Δ)
  | impR {ℓ Γ Δ A B} :
    Derivation (insert A Γ ⟹[ℓ] insert B Δ) → Derivation (Γ ⟹[ℓ] insert (A 🡒 B) Δ)
  | boxGL {Γ : FormulaFinset α} {A} :
    Derivation (insert (□A) (Γ.box ∪ Γ) ⟹[0] {A}) → Derivation (Γ.box ⟹[0] {□A})
  | boxL {Γ Δ A} : Derivation (insert A Γ ⟹[1] Δ) → Derivation (insert (□A) Γ ⟹[1] Δ)
  | liftUp₀₁ {Γ Δ} : Derivation (Γ ⟹[0] Δ) → Derivation (Γ ⟹[1] Δ)
  | liftUp₁₂ {Γ Δ : FormulaFinset α} :
    Derivation (Γ.box ⟹[1] Δ.box) → Derivation (Γ.box ⟹[2] Δ.box)

/-- Applications of weakening are not counted.
- [Nog26, Section 2] -/
@[grind =]
def Derivation.height {S : LayeredSequent α} : Derivation S → ℕ
  | axm .. | botL _ => 0
  | wk D _ _ => D.height
  | impL D₁ D₂ => max D₁.height D₂.height + 1
  | impR D | boxGL D | boxL D | liftUp₀₁ D | liftUp₁₂ D => D.height + 1

/-- - [Nog26, Definitions 3.1, 6.1] -/
def Derivable (S : LayeredSequent α) : Prop := Nonempty (Derivation S)

end logicD

@[inherit_doc] scoped[Modal] notation:45 "⊢ᴳ[𝐃]! " S:50 => logicD.Derivation S
@[inherit_doc] scoped[Modal] notation:45 "⊢ᴳ[𝐃] " S:50 => logicD.Derivable S
scoped[Modal] notation:45 "⊬ᴳ[𝐃] " S:50 => ¬logicD.Derivable S

section

variable {α : Type*} [DecidableEq α]

/-- - [Nog26, Definition 3.1] -/
def logicS : Logic α := {A | ⊢ᴳ[𝐃] ∅ ⟹[1] {A}}

/-- - [Nog26, Definition 6.1] -/
def logicD : Logic α := {A | ⊢ᴳ[𝐃] ∅ ⟹[2] {A}}

@[inherit_doc] scoped[Modal] notation "𝐒" => logicS
@[inherit_doc] scoped[Modal] notation "𝐃" => logicD

end

namespace logicD

variable {α : Type*} [DecidableEq α] {ℓ : Fin 3} {Γ Γ' Δ Δ' Θ : FormulaFinset α}
  {A B : Formula α}

namespace Derivable

lemma wk (d : ⊢ᴳ[𝐃] Γ ⟹[ℓ] Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐃] Γ' ⟹[ℓ] Δ' :=
  Nonempty.map (.wk · hΓ hΔ) d

lemma impL (d₁ : ⊢ᴳ[𝐃] Γ ⟹[ℓ] insert A Δ) (d₂ : ⊢ᴳ[𝐃] insert B Γ ⟹[ℓ] Δ) :
    ⊢ᴳ[𝐃] insert (A 🡒 B) Γ ⟹[ℓ] Δ :=
  Nonempty.map2 .impL d₁ d₂

lemma impR (d : ⊢ᴳ[𝐃] insert A Γ ⟹[ℓ] insert B Δ) : ⊢ᴳ[𝐃] Γ ⟹[ℓ] insert (A 🡒 B) Δ :=
  Nonempty.map .impR d

lemma boxGL (d : ⊢ᴳ[𝐃] insert (□A) (Γ.box ∪ Γ) ⟹[0] {A}) : ⊢ᴳ[𝐃] Γ.box ⟹[0] {□A} :=
  Nonempty.map .boxGL d

lemma boxL (d : ⊢ᴳ[𝐃] insert A Γ ⟹[1] Δ) : ⊢ᴳ[𝐃] insert (□A) Γ ⟹[1] Δ :=
  Nonempty.map .boxL d

lemma liftUp₀₁ (d : ⊢ᴳ[𝐃] Γ ⟹[0] Δ) : ⊢ᴳ[𝐃] Γ ⟹[1] Δ :=
  Nonempty.map .liftUp₀₁ d

lemma liftUp₁₂ (d : ⊢ᴳ[𝐃] Γ.box ⟹[1] Δ.box) : ⊢ᴳ[𝐃] Γ.box ⟹[2] Δ.box :=
  Nonempty.map .liftUp₁₂ d

@[elab_as_elim, induction_eliminator]
theorem rec {motive : (S : LayeredSequent α) → ⊢ᴳ[𝐃] S → Prop}
    (axm : ∀ ℓ a, motive _ ⟨.axm ℓ a⟩) (botL : ∀ ℓ, motive _ ⟨.botL ℓ⟩)
    (wk : ∀ {ℓ Γ Γ' Δ Δ'} (d : ⊢ᴳ[𝐃] Γ ⟹[ℓ] Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ'),
      motive _ d → motive _ (d.wk hΓ hΔ))
    (impL : ∀ {ℓ Γ Δ A B} (d₁ : ⊢ᴳ[𝐃] Γ ⟹[ℓ] insert A Δ) (d₂ : ⊢ᴳ[𝐃] insert B Γ ⟹[ℓ] Δ),
      motive _ d₁ → motive _ d₂ → motive _ (.impL d₁ d₂))
    (impR : ∀ {ℓ Γ Δ A B} (d : ⊢ᴳ[𝐃] insert A Γ ⟹[ℓ] insert B Δ), motive _ d → motive _ d.impR)
    (boxGL : ∀ {Γ : FormulaFinset α} {A} (d : ⊢ᴳ[𝐃] insert (□A) (Γ.box ∪ Γ) ⟹[0] {A}),
      motive _ d → motive _ d.boxGL)
    (boxL : ∀ {Γ Δ A} (d : ⊢ᴳ[𝐃] insert A Γ ⟹[1] Δ), motive _ d → motive _ d.boxL)
    (liftUp₀₁ : ∀ {Γ Δ} (d : ⊢ᴳ[𝐃] Γ ⟹[0] Δ), motive _ d → motive _ d.liftUp₀₁)
    (liftUp₁₂ : ∀ {Γ Δ : FormulaFinset α} (d : ⊢ᴳ[𝐃] Γ.box ⟹[1] Δ.box),
      motive _ d → motive _ d.liftUp₁₂) :
    ∀ {S} (h : ⊢ᴳ[𝐃] S), motive S h := by
  rintro S ⟨D⟩
  induction D with
  | axm ℓ a => exact axm ℓ a
  | botL ℓ => exact botL ℓ
  | wk _ hΓ hΔ ih => exact wk _ hΓ hΔ ih
  | impL _ _ ih₁ ih₂ => exact impL _ _ ih₁ ih₂
  | impR _ ih => exact impR _ ih
  | boxGL _ ih => exact boxGL _ ih
  | boxL _ ih => exact boxL _ ih
  | liftUp₀₁ _ ih => exact liftUp₀₁ _ ih
  | liftUp₁₂ _ ih => exact liftUp₁₂ _ ih

lemma liftUp₁₂_singleton (d : ⊢ᴳ[𝐃] Γ.box ⟹[1] {□A}) : ⊢ᴳ[𝐃] Γ.box ⟹[2] {□A} :=
  liftUp₁₂ (Δ := {A}) d

/-- - [Nog26, Lemmas 3.3, 6.3] -/
lemma refl (ℓ : Fin 3) (A : Formula α) : ⊢ᴳ[𝐃] {A} ⟹[ℓ] {A} := by
  induction A generalizing ℓ with
  | atom a => exact ⟨.axm ℓ a⟩
  | falsum => exact wk ⟨.botL ℓ⟩ (by grind) (by grind)
  | imp B C ihB ihC =>
    have h₁ : ⊢ᴳ[𝐃] {B} ⟹[ℓ] insert B {C} := wk (ihB ℓ) (by grind) (by grind)
    have h₂ : ⊢ᴳ[𝐃] insert C {B} ⟹[ℓ] {C} := wk (ihC ℓ) (by grind) (by grind)
    have h₃ : ⊢ᴳ[𝐃] insert B {B 🡒 C} ⟹[ℓ] insert C ∅ := wk (impL h₁ h₂) (by grind) (by grind)
    exact wk (impR h₃) (by grind) (by grind)
  | box B ih =>
    have h₀ : ⊢ᴳ[𝐃] {□B} ⟹[0] {□B} := boxGL (Γ := {B}) (wk (ih 0) (by grind) (by grind))
    match ℓ with
    | 0 => exact h₀
    | 1 => exact liftUp₀₁ h₀
    | 2 => exact liftUp₁₂_singleton (Γ := {B}) (liftUp₀₁ h₀)

lemma union (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) : ⊢ᴳ[𝐃] Γ ⟹[ℓ] Δ :=
  wk (refl ℓ A) (by grind) (by grind)

lemma botL_mem (h : ⊥ ∈ Γ) : ⊢ᴳ[𝐃] Γ ⟹[ℓ] Δ :=
  wk ⟨.botL ℓ⟩ (by grind) (by grind)

lemma andL (d : ⊢ᴳ[𝐃] insert A (insert B Γ) ⟹[ℓ] Δ) : ⊢ᴳ[𝐃] insert (A ⋏ B) Γ ⟹[ℓ] Δ := by
  have h₁ : ⊢ᴳ[𝐃] Γ ⟹[ℓ] insert (A 🡒 ∼B) Δ :=
    impR (impR (wk d (by grind) (by grind)))
  exact impL h₁ (botL_mem (by grind))

lemma andR (d₁ : ⊢ᴳ[𝐃] Γ ⟹[ℓ] insert A Δ) (d₂ : ⊢ᴳ[𝐃] Γ ⟹[ℓ] insert B Δ) :
    ⊢ᴳ[𝐃] Γ ⟹[ℓ] insert (A ⋏ B) Δ := by
  have h₁ : ⊢ᴳ[𝐃] insert (∼B) Γ ⟹[ℓ] Δ :=
    impL (wk d₂ (by grind) (by grind)) (botL_mem (by grind))
  have h₂ : ⊢ᴳ[𝐃] insert (A 🡒 ∼B) Γ ⟹[ℓ] insert ⊥ Δ :=
    impL (wk d₁ (by grind) (by grind)) (wk h₁ (by grind) (by grind))
  exact impR h₂

lemma orL (d₁ : ⊢ᴳ[𝐃] insert A Γ ⟹[ℓ] Δ) (d₂ : ⊢ᴳ[𝐃] insert B Γ ⟹[ℓ] Δ) :
    ⊢ᴳ[𝐃] insert (A ⋎ B) Γ ⟹[ℓ] Δ :=
  impL (impR (wk d₁ (by grind) (by grind))) d₂

lemma orR (d : ⊢ᴳ[𝐃] Γ ⟹[ℓ] insert A (insert B Δ)) : ⊢ᴳ[𝐃] Γ ⟹[ℓ] insert (A ⋎ B) Δ :=
  impR (impL (wk d (by grind) (by grind)) (botL_mem (by grind)))

/-- The rule `□K4`.
- [Nog26, Lemmas 5.1, 8.1] -/
lemma boxK4 (d : ⊢ᴳ[𝐃] Γ.box ∪ Γ ⟹[0] {A}) (ℓ : Fin 3) : ⊢ᴳ[𝐃] Γ.box ⟹[ℓ] {□A} := by
  have h₀ : ⊢ᴳ[𝐃] Γ.box ⟹[0] {□A} := boxGL (wk d (by grind) (by grind))
  match ℓ with
  | 0 => exact h₀
  | 1 => exact liftUp₀₁ h₀
  | 2 => exact liftUp₁₂_singleton (liftUp₀₁ h₀)

lemma impL_image {β : Type*} [DecidableEq β] {f g : β → Formula α} {P : Finset β}
    (d : ∀ I ⊆ P, ⊢ᴳ[𝐃] I.image g ∪ Γ ⟹[ℓ] Δ ∪ (P \ I).image f) :
    ⊢ᴳ[𝐃] P.image (fun p ↦ f p 🡒 g p) ∪ Γ ⟹[ℓ] Δ := by
  induction P using Finset.induction_on generalizing Γ Δ with
  | empty => exact (d ∅ (by grind)).wk (by grind) (by grind)
  | insert p P hp ih =>
    have d₁ := ih (Γ := Γ) (Δ := insert (f p) Δ) fun I hI ↦
      (d I (by grind)).wk (by grind) (by grind)
    have d₂ := ih (Γ := insert (g p) Γ) (Δ := Δ) fun I hI ↦
      (d (insert p I) (by grind)).wk (by grind) (by grind)
    have d₃ := impL (A := f p) (B := g p) d₁ (d₂.wk (by grind) (by grind))
    exact d₃.wk (by grind) (by grind)

end Derivable

end logicD

end Modal

namespace Modal.logicD.Derivation

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι] {ℓ : Fin 3}
  {Γ Δ : FormulaFinset α} {A B : Formula α} {S : LayeredSequent α} {P I : Finset ι}
  {f g : ι → Formula α}

@[elab_as_elim]
theorem height_induction {motive : (S : LayeredSequent α) → ⊢ᴳ[𝐃]! S → Prop}
    (axm : ∀ ℓ a, motive _ (axm ℓ a)) (botL : ∀ ℓ, motive _ (botL ℓ))
    (wk : ∀ {ℓ Γ Γ' Δ Δ'} (D : ⊢ᴳ[𝐃]! Γ ⟹[ℓ] Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ'),
      motive _ D → motive _ (wk D hΓ hΔ))
    (impL : ∀ {ℓ Γ Δ A B} (D₁ : ⊢ᴳ[𝐃]! Γ ⟹[ℓ] insert A Δ) (D₂ : ⊢ᴳ[𝐃]! insert B Γ ⟹[ℓ] Δ),
      (∀ {T} (D' : ⊢ᴳ[𝐃]! T), D'.height ≤ max D₁.height D₂.height → motive T D') →
        motive _ (impL D₁ D₂))
    (impR : ∀ {ℓ Γ Δ A B} (D : ⊢ᴳ[𝐃]! insert A Γ ⟹[ℓ] insert B Δ),
      (∀ {T} (D' : ⊢ᴳ[𝐃]! T), D'.height ≤ D.height → motive T D') → motive _ (impR D))
    (boxGL : ∀ {Γ : FormulaFinset α} {A} (D : ⊢ᴳ[𝐃]! insert (□A) (Γ.box ∪ Γ) ⟹[0] {A}),
      (∀ {T} (D' : ⊢ᴳ[𝐃]! T), D'.height ≤ D.height → motive T D') → motive _ (boxGL D))
    (boxL : ∀ {Γ Δ A} (D : ⊢ᴳ[𝐃]! insert A Γ ⟹[1] Δ),
      (∀ {T} (D' : ⊢ᴳ[𝐃]! T), D'.height ≤ D.height → motive T D') → motive _ (boxL D))
    (liftUp₀₁ : ∀ {Γ Δ} (D : ⊢ᴳ[𝐃]! Γ ⟹[0] Δ),
      (∀ {T} (D' : ⊢ᴳ[𝐃]! T), D'.height ≤ D.height → motive T D') → motive _ (liftUp₀₁ D))
    (liftUp₁₂ : ∀ {Γ Δ : FormulaFinset α} (D : ⊢ᴳ[𝐃]! Γ.box ⟹[1] Δ.box),
      (∀ {T} (D' : ⊢ᴳ[𝐃]! T), D'.height ≤ D.height → motive T D') → motive _ (liftUp₁₂ D))
    (D : ⊢ᴳ[𝐃]! S) : motive S D := by
  suffices h : ∀ n {S} (D : ⊢ᴳ[𝐃]! S), D.height ≤ n → motive S D from h _ D le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro S D hD
    induction D with
    | axm ℓ a => exact axm ℓ a
    | botL ℓ => exact botL ℓ
    | wk D hΓ hΔ ih => exact wk D hΓ hΔ (ih hD)
    | impL D₁ D₂ => exact impL D₁ D₂ fun D' h ↦ ihn _ (by grind) D' le_rfl
    | impR D => exact impR D fun D' h ↦ ihn _ (by grind) D' le_rfl
    | boxGL D => exact boxGL D fun D' h ↦ ihn _ (by grind) D' le_rfl
    | boxL D => exact boxL D fun D' h ↦ ihn _ (by grind) D' le_rfl
    | liftUp₀₁ D => exact liftUp₀₁ D fun D' h ↦ ihn _ (by grind) D' le_rfl
    | liftUp₁₂ D => exact liftUp₁₂ D fun D' h ↦ ihn _ (by grind) D' le_rfl

/-- - [Nog26] -/
lemma erase_bot (D : ⊢ᴳ[𝐃]! Γ ⟹[ℓ] Δ) :
    ∃ D' : ⊢ᴳ[𝐃]! Γ ⟹[ℓ] Δ.erase ⊥, D'.height ≤ D.height := by
  generalize hS : (Γ ⟹[ℓ] Δ) = S at D
  induction D generalizing Γ Δ ℓ with cases hS
  | axm ℓ a =>
    exact ⟨wk (axm ℓ a) (by grind) (by grind), by grind⟩
  | botL ℓ =>
    exact ⟨wk (botL ℓ) (by grind) (by grind), by grind⟩
  | wk _ hΓ hΔ ih =>
    obtain ⟨D, hD⟩ := ih rfl
    exact ⟨wk D hΓ (by grind), by grind⟩
  | impL _ _ ih₁ ih₂ =>
    obtain ⟨D₁, h₁⟩ := ih₁ rfl
    obtain ⟨D₂, h₂⟩ := ih₂ rfl
    exact ⟨impL (wk D₁ (by grind) (by grind)) D₂, by grind⟩
  | @impR _ Γ' Δ' E F _ ih =>
    obtain ⟨D, hD⟩ := ih rfl
    exact ⟨wk (impR (Γ := Γ') (Δ := Δ'.erase ⊥) (A := E) (B := F) (wk D (by grind) (by grind)))
      (by grind) (by grind), by grind⟩
  | boxGL D =>
    exact ⟨wk (boxGL D) (by grind) (by grind), by grind⟩
  | boxL _ ih =>
    obtain ⟨D, hD⟩ := ih rfl
    exact ⟨boxL D, by grind⟩
  | liftUp₀₁ _ ih =>
    obtain ⟨D, hD⟩ := ih rfl
    exact ⟨liftUp₀₁ D, by grind⟩
  | liftUp₁₂ D =>
    exact ⟨wk (liftUp₁₂ D) (by grind) (by grind), by grind⟩

/-- - [Nog26] -/
lemma invImpR (D : ⊢ᴳ[𝐃]! Γ ⟹[ℓ] Δ) (hAB : A 🡒 B ∈ Δ) :
    ∃ D' : ⊢ᴳ[𝐃]! insert A Γ ⟹[ℓ] insert B (Δ.erase (A 🡒 B)), D'.height ≤ D.height := by
  generalize hS : (Γ ⟹[ℓ] Δ) = S at D
  induction D generalizing Γ Δ ℓ with cases hS
  | axm ℓ a =>
    grind
  | botL ℓ =>
    grind
  | @wk ℓ' Γ₀ Γ' Δ₀ Δ' D hΓ hΔ ih =>
    by_cases hΔ₀ : A 🡒 B ∈ Δ₀
    · obtain ⟨D', hD'⟩ := ih hΔ₀ rfl
      exact ⟨wk D' (by grind) (by grind), by grind⟩
    · exact ⟨wk D (by grind) (by grind), by grind⟩
  | @impL ℓ' Γ' Δ' E F D₁ _ ih₁ ih₂ =>
    by_cases hE : E = A 🡒 B
    · subst hE
      obtain ⟨D, hD⟩ := ih₁ (by grind) rfl
      exact ⟨wk D (by grind) (by grind), by grind⟩
    · obtain ⟨D₁', h₁⟩ := ih₁ (by grind) rfl
      obtain ⟨D₂', h₂⟩ := ih₂ (by grind) rfl
      use wk (impL (Γ := insert A Γ') (Δ := insert B (Δ'.erase (A 🡒 B))) (A := E) (B := F)
        (wk D₁' (by grind) (by grind)) (wk D₂' (by grind) (by grind))) (by grind) (by grind)
      exact Nat.succ_le_succ (max_le_max h₁ h₂)
  | @impR ℓ' Γ' Δ' E F D ih =>
    by_cases hE : E 🡒 F = A 🡒 B
    · obtain ⟨rfl, rfl⟩ := Formula.imp.inj hE
      by_cases hΔ' : E 🡒 F ∈ Δ'
      · obtain ⟨D', hD'⟩ := ih (by grind) rfl
        exact ⟨wk D' (by grind) (by grind), by grind⟩
      · exact ⟨wk D (by grind) (by grind), by grind⟩
    · obtain ⟨D', hD'⟩ := ih (by grind) rfl
      exact ⟨wk (impR (Γ := insert A Γ') (Δ := insert B (Δ'.erase (A 🡒 B))) (A := E) (B := F)
        (wk D' (by grind) (by grind))) (by grind) (by grind), by grind⟩
  | boxGL D =>
    grind
  | @boxL Γ' Δ' E _ ih =>
    obtain ⟨D', hD'⟩ := ih hAB rfl
    exact ⟨wk (boxL (Γ := insert A Γ') (Δ := insert B (Δ'.erase (A 🡒 B))) (A := E)
      (wk D' (by grind) (by grind))) (by grind) (by grind), by grind⟩
  | liftUp₀₁ _ ih =>
    obtain ⟨D', hD'⟩ := ih hAB rfl
    exact ⟨liftUp₀₁ D', by grind⟩
  | liftUp₁₂ D =>
    grind

/-- - [Nog26] -/
lemma invImpL_left (D : ⊢ᴳ[𝐃]! Γ ⟹[ℓ] Δ) (hAB : A 🡒 B ∈ Γ) :
    ∃ D' : ⊢ᴳ[𝐃]! Γ.erase (A 🡒 B) ⟹[ℓ] insert A Δ, D'.height ≤ D.height := by
  generalize hS : (Γ ⟹[ℓ] Δ) = S at D
  induction D generalizing Γ Δ ℓ with cases hS
  | axm ℓ a =>
    grind
  | botL ℓ =>
    grind
  | @wk ℓ' Γ₀ Γ' Δ₀ Δ' D hΓ hΔ ih =>
    by_cases hΓ₀ : A 🡒 B ∈ Γ₀
    · obtain ⟨D', hD'⟩ := ih hΓ₀ rfl
      exact ⟨wk D' (by grind) (by grind), by grind⟩
    · exact ⟨wk D (by grind) (by grind), by grind⟩
  | @impL ℓ Γ Δ E F D₁ D₂ ih₁ ih₂ =>
    by_cases hE : E 🡒 F = A 🡒 B
    · obtain ⟨rfl, rfl⟩ := Formula.imp.inj hE
      by_cases hΓ : E 🡒 F ∈ Γ
      · obtain ⟨D₃, h₃⟩ := ih₁ hΓ rfl
        exact ⟨wk D₃ (by grind) (by grind), by grind⟩
      · exact ⟨wk D₁ (by grind) (by grind), by grind⟩
    · obtain ⟨D₃, h₃⟩ := ih₁ (by grind) rfl
      obtain ⟨D₄, h₄⟩ := ih₂ (by grind) rfl
      use wk (impL (Γ := Γ.erase (A 🡒 B)) (Δ := insert A Δ) (A := E) (B := F)
        (wk D₃ (by grind) (by grind)) (wk D₄ (by grind) (by grind))) (by grind) (by grind)
      exact Nat.succ_le_succ (max_le_max h₃ h₄)
  | @impR ℓ' Γ' Δ' E F _ ih =>
    obtain ⟨D', hD'⟩ := ih (by grind) rfl
    exact ⟨wk (impR (Γ := Γ'.erase (A 🡒 B)) (Δ := insert A Δ') (A := E) (B := F)
      (wk D' (by grind) (by grind))) (by grind) (by grind), by grind⟩
  | boxGL D =>
    grind
  | @boxL Γ' Δ' E _ ih =>
    obtain ⟨D', hD'⟩ := ih (by grind) rfl
    exact ⟨wk (boxL (Γ := Γ'.erase (A 🡒 B)) (Δ := insert A Δ') (A := E)
      (wk D' (by grind) (by grind))) (by grind) (by grind), by grind⟩
  | liftUp₀₁ _ ih =>
    obtain ⟨D', hD'⟩ := ih hAB rfl
    exact ⟨liftUp₀₁ D', by grind⟩
  | liftUp₁₂ D =>
    grind

/-- - [Nog26] -/
lemma invImpL_right (D : ⊢ᴳ[𝐃]! Γ ⟹[ℓ] Δ) (hAB : A 🡒 B ∈ Γ) :
    ∃ D' : ⊢ᴳ[𝐃]! insert B (Γ.erase (A 🡒 B)) ⟹[ℓ] Δ, D'.height ≤ D.height := by
  generalize hS : (Γ ⟹[ℓ] Δ) = S at D
  induction D generalizing Γ Δ ℓ with cases hS
  | axm ℓ a =>
    grind
  | botL ℓ =>
    grind
  | @wk ℓ' Γ₀ Γ' Δ₀ Δ' D hΓ hΔ ih =>
    by_cases hΓ₀ : A 🡒 B ∈ Γ₀
    · obtain ⟨D', hD'⟩ := ih hΓ₀ rfl
      exact ⟨wk D' (by grind) (by grind), by grind⟩
    · exact ⟨wk D (by grind) (by grind), by grind⟩
  | @impL ℓ Γ Δ E F D₁ D₂ ih₁ ih₂ =>
    by_cases hE : E 🡒 F = A 🡒 B
    · obtain ⟨rfl, rfl⟩ := Formula.imp.inj hE
      by_cases hΓ : E 🡒 F ∈ Γ
      · obtain ⟨D₃, h₃⟩ := ih₂ (by grind) rfl
        exact ⟨wk D₃ (by grind) (by grind), by grind⟩
      · exact ⟨wk D₂ (by grind) (by grind), by grind⟩
    · obtain ⟨D₃, h₃⟩ := ih₁ (by grind) rfl
      obtain ⟨D₄, h₄⟩ := ih₂ (by grind) rfl
      use wk (impL (Γ := insert B (Γ.erase (A 🡒 B))) (Δ := Δ) (A := E) (B := F)
        (wk D₃ (by grind) (by grind)) (wk D₄ (by grind) (by grind))) (by grind) (by grind)
      exact Nat.succ_le_succ (max_le_max h₃ h₄)
  | @impR ℓ' Γ' Δ' E F _ ih =>
    obtain ⟨D', hD'⟩ := ih (by grind) rfl
    exact ⟨impR (Γ := insert B (Γ'.erase (A 🡒 B))) (A := E) (B := F)
      (wk D' (by grind) (by grind)), by grind⟩
  | boxGL D =>
    grind
  | @boxL Γ' Δ' E _ ih =>
    obtain ⟨D', hD'⟩ := ih (by grind) rfl
    exact ⟨wk (boxL (Γ := insert B (Γ'.erase (A 🡒 B))) (Δ := Δ') (A := E)
      (wk D' (by grind) (by grind))) (by grind) (by grind), by grind⟩
  | liftUp₀₁ _ ih =>
    obtain ⟨D', hD'⟩ := ih hAB rfl
    exact ⟨liftUp₀₁ D', by grind⟩
  | liftUp₁₂ D =>
    grind

lemma invImps (D : ⊢ᴳ[𝐃]! Γ ⟹[ℓ] Δ) (hfg : Function.Injective fun i ↦ f i 🡒 g i)
    (hP : P.image (fun i ↦ f i 🡒 g i) ⊆ Γ) (hI : I ⊆ P) :
    ∃ D' : ⊢ᴳ[𝐃]! Γ \ P.image (fun i ↦ f i 🡒 g i) ∪ I.image g ⟹[ℓ] Δ ∪ (P \ I).image f,
      D'.height ≤ D.height := by
  induction P using Finset.induction_on generalizing I with
  | empty => exact ⟨D.wk (by grind) (by grind), by grind⟩
  | insert p P hp ih =>
    have hp' : f p 🡒 g p ∉ P.image fun i ↦ f i 🡒 g i := by
      by_contra h₁
      obtain ⟨q, hq, e⟩ := Finset.mem_image.mp h₁
      exact hp (hfg e ▸ hq)
    have hP' : P.image (fun i ↦ f i 🡒 g i) ⊆ Γ :=
      (Finset.image_subset_image (Finset.subset_insert _ _)).trans hP
    have hpΓ : f p 🡒 g p ∈ Γ := hP (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
    have hPp : (insert p P).image (fun i ↦ f i 🡒 g i) =
        insert (f p 🡒 g p) (P.image fun i ↦ f i 🡒 g i) :=
      Finset.image_insert _ _ _
    by_cases hpI : p ∈ I
    · obtain ⟨D₁, h₁⟩ := ih (I := I.erase p) hP' (by grind)
      obtain ⟨D₂, h₂⟩ := D₁.invImpL_right (A := f p) (B := g p) (by grind)
      have h₃ : g p ∈ I.image g := Finset.mem_image_of_mem _ hpI
      have h₄ : (I.erase p).image g ⊆ I.image g :=
        Finset.image_subset_image (Finset.erase_subset _ _)
      have h₅ : (P \ I.erase p).image f ⊆ (insert p P \ I).image f :=
        Finset.image_subset_image (by grind)
      exact ⟨D₂.wk (by grind) (by grind), by grind⟩
    · obtain ⟨D₁, h₁⟩ := ih (I := I) hP' (by grind)
      obtain ⟨D₂, h₂⟩ := D₁.invImpL_left (A := f p) (B := g p) (by grind)
      have h₃ : f p ∈ (insert p P \ I).image f := Finset.mem_image_of_mem _ (by grind)
      have h₄ : (P \ I).image f ⊆ (insert p P \ I).image f :=
        Finset.image_subset_image (by grind)
      exact ⟨D₂.wk (by grind) (by grind), by grind⟩

end Modal.logicD.Derivation

end
