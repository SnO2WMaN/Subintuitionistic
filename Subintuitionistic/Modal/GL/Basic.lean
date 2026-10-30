module

public import Subintuitionistic.Modal.Sequent

/-!
# The sequent calculus of `𝐆𝐋`
-/

@[expose] public section

namespace Modal

namespace logicGL

variable {α : Type*} [DecidableEq α]

inductive Derivation : Sequent α → Type _
  | axm (a : α) : Derivation ({#a} ⟹ {#a})
  | botL : Derivation ({⊥} ⟹ ∅)
  | wk {Γ Γ' Δ Δ'} : Derivation (Γ ⟹ Δ) → Γ ⊆ Γ' → Δ ⊆ Δ' → Derivation (Γ' ⟹ Δ')
  | impL {Γ Δ A B} :
    Derivation (Γ ⟹ insert A Δ) → Derivation (insert B Γ ⟹ Δ) → Derivation (insert (A 🡒 B) Γ ⟹ Δ)
  | impR {Γ Δ A B} : Derivation (insert A Γ ⟹ insert B Δ) → Derivation (Γ ⟹ insert (A 🡒 B) Δ)
  | boxGL {Γ : FormulaFinset α} {A} :
    Derivation (insert (□A) (Γ.box ∪ Γ) ⟹ {A}) → Derivation (Γ.box ⟹ {□A})

def Derivable (S : Sequent α) : Prop := Nonempty (Derivation S)

end logicGL

scoped[Modal] notation:45 "⊢ᴳ[𝐆𝐋]! " S:50 => logicGL.Derivation S
scoped[Modal] notation:45 "⊢ᴳ[𝐆𝐋] " S:50 => logicGL.Derivable S
scoped[Modal] notation:45 "⊬ᴳ[𝐆𝐋] " S:50 => ¬logicGL.Derivable S

section

variable {α : Type*} [DecidableEq α]

def logicGL : Logic α := {A | ⊢ᴳ[𝐆𝐋] ∅ ⟹ {A}}

scoped[Modal] notation "𝐆𝐋" => logicGL

end

namespace logicGL.Derivable

variable {α : Type*} [DecidableEq α] {Γ Γ' Δ Δ' : FormulaFinset α} {A B : Formula α}

lemma axm (a : α) : ⊢ᴳ[𝐆𝐋] {#a} ⟹ {#a} := ⟨.axm a⟩

lemma botL : ⊢ᴳ[𝐆𝐋] ({⊥} ⟹ ∅ : Sequent α) := ⟨.botL⟩

lemma wk (d : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐆𝐋] Γ' ⟹ Δ' :=
  Nonempty.map (.wk · hΓ hΔ) d

lemma impL (d₁ : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert A Δ) (d₂ : ⊢ᴳ[𝐆𝐋] insert B Γ ⟹ Δ) :
    ⊢ᴳ[𝐆𝐋] insert (A 🡒 B) Γ ⟹ Δ :=
  Nonempty.map2 .impL d₁ d₂

lemma impR (d : ⊢ᴳ[𝐆𝐋] insert A Γ ⟹ insert B Δ) : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert (A 🡒 B) Δ :=
  Nonempty.map .impR d

lemma boxGL (d : ⊢ᴳ[𝐆𝐋] insert (□A) (Γ.box ∪ Γ) ⟹ {A}) : ⊢ᴳ[𝐆𝐋] Γ.box ⟹ {□A} :=
  Nonempty.map .boxGL d

@[elab_as_elim, induction_eliminator]
theorem rec {motive : (S : Sequent α) → ⊢ᴳ[𝐆𝐋] S → Prop}
    (axm : ∀ a, motive _ (axm a)) (botL : motive _ botL)
    (wk : ∀ {Γ Γ' Δ Δ'} (d : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ'),
      motive _ d → motive _ (d.wk hΓ hΔ))
    (impL : ∀ {Γ Δ A B} (d₁ : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert A Δ) (d₂ : ⊢ᴳ[𝐆𝐋] insert B Γ ⟹ Δ),
      motive _ d₁ → motive _ d₂ → motive _ (impL d₁ d₂))
    (impR : ∀ {Γ Δ A B} (d : ⊢ᴳ[𝐆𝐋] insert A Γ ⟹ insert B Δ), motive _ d → motive _ d.impR)
    (boxGL : ∀ {Γ : FormulaFinset α} {A} (d : ⊢ᴳ[𝐆𝐋] insert (□A) (Γ.box ∪ Γ) ⟹ {A}),
      motive _ d → motive _ d.boxGL) :
    ∀ {S} (h : ⊢ᴳ[𝐆𝐋] S), motive S h := by
  rintro S ⟨D⟩
  induction D with
  | axm a => exact axm a
  | botL => exact botL
  | wk _ hΓ hΔ ih => exact wk _ hΓ hΔ ih
  | impL _ _ ih₁ ih₂ => exact impL _ _ ih₁ ih₂
  | impR _ ih => exact impR _ ih
  | boxGL _ ih => exact boxGL _ ih

lemma refl (A : Formula α) : ⊢ᴳ[𝐆𝐋] {A} ⟹ {A} := by
  induction A with
  | atom a => exact axm a
  | falsum => exact botL.wk (by grind) (by grind)
  | imp B C ihB ihC =>
    have h₁ : ⊢ᴳ[𝐆𝐋] {B} ⟹ insert B {C} := ihB.wk (by grind) (by grind)
    have h₂ : ⊢ᴳ[𝐆𝐋] insert C {B} ⟹ {C} := ihC.wk (by grind) (by grind)
    have h₃ : ⊢ᴳ[𝐆𝐋] insert B {B 🡒 C} ⟹ insert C ∅ := (impL h₁ h₂).wk (by grind) (by grind)
    exact h₃.impR.wk (by grind) (by grind)
  | box B ih => exact boxGL (Γ := {B}) (ih.wk (by grind) (by grind))

@[grind .] lemma axm_mem (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ :=
  (refl A).wk (by grind) (by grind)

@[grind .] lemma botL_mem (h : ⊥ ∈ Γ) : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ := botL.wk (by grind) (by grind)

@[grind .] lemma impL_of_mem (hAB : A 🡒 B ∈ Γ) (d₁ : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert A Δ)
    (d₂ : ⊢ᴳ[𝐆𝐋] insert B Γ ⟹ Δ) : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ :=
  (impL d₁ d₂).wk (Finset.insert_subset hAB subset_rfl) subset_rfl

@[grind .] lemma impR_of_mem (hAB : A 🡒 B ∈ Δ) (d : ⊢ᴳ[𝐆𝐋] insert A Γ ⟹ insert B Δ) :
    ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ :=
  d.impR.wk subset_rfl (Finset.insert_subset hAB subset_rfl)

@[grind .] lemma boxGL_of_mem {Θ : FormulaFinset α} (hΘ : Θ.box ⊆ Γ) (hA : □A ∈ Δ)
    (d : ⊢ᴳ[𝐆𝐋] insert (□A) (Θ.box ∪ Θ) ⟹ {A}) : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ :=
  d.boxGL.wk hΘ (Finset.singleton_subset_iff.mpr hA)

end logicGL.Derivable

end Modal

end
