module

public import Subintuitionistic.Modal.Sequent
public import Mathlib.Data.Finset.Image

/-!
# The sequent calculus of `GL`

`logicGL.Derivation` is a cut-free sequent calculus in the style of G3: initial sequents carry
contexts and the principal formula of a rule stays in its conclusion, so weakening and
contraction are built in.
-/

@[expose] public section

namespace Modal

namespace logicGL

variable {α : Type*} [DecidableEq α]

/-- - [SV82] -/
inductive Derivation : Sequent α → Type _
  | axm {Γ Δ A} : A ∈ Γ → A ∈ Δ → Derivation (Γ ⟹ Δ)
  | botL {Γ Δ} : ⊥ ∈ Γ → Derivation (Γ ⟹ Δ)
  | impL {Γ Δ A B} :
    A 🡒 B ∈ Γ → Derivation (Γ ⟹ insert A Δ) → Derivation (insert B Γ ⟹ Δ) → Derivation (Γ ⟹ Δ)
  | impR {Γ Δ A B} : A 🡒 B ∈ Δ → Derivation (insert A Γ ⟹ insert B Δ) → Derivation (Γ ⟹ Δ)
  | boxGL {Γ Δ Θ A} :
    Θ.box ⊆ Γ → □A ∈ Δ → Derivation (insert (□A) (Θ ∪ Θ.box) ⟹ {A}) → Derivation (Γ ⟹ Δ)

/-- - [SV82] -/
def Derivable (S : Sequent α) : Prop := Nonempty (Derivation S)

end logicGL

@[inherit_doc] scoped[Modal] notation:45 "⊢ᴳ[𝐆𝐋]! " S:50 => logicGL.Derivation S
@[inherit_doc] scoped[Modal] notation:45 "⊢ᴳ[𝐆𝐋] " S:50 => logicGL.Derivable S
scoped[Modal] notation:45 "⊬ᴳ[𝐆𝐋] " S:50 => ¬logicGL.Derivable S

section

variable {α : Type*} [DecidableEq α]

/-- - [SV82] -/
def logicGL : Logic α := {A | ⊢ᴳ[𝐆𝐋] ∅ ⟹ {A}}

@[inherit_doc] scoped[Modal] notation "𝐆𝐋" => logicGL

end

namespace logicGL.Derivable

variable {α : Type*} [DecidableEq α] {Γ Δ Θ : FormulaFinset α} {A B : Formula α}

@[grind .] lemma axm (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ := ⟨.axm hΓ hΔ⟩

@[grind .] lemma botL (h : ⊥ ∈ Γ) : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ := ⟨.botL h⟩

@[grind .] lemma impL (hAB : A 🡒 B ∈ Γ) (d₁ : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert A Δ)
    (d₂ : ⊢ᴳ[𝐆𝐋] insert B Γ ⟹ Δ) : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ :=
  Nonempty.map2 (.impL hAB) d₁ d₂

@[grind .] lemma impR (hAB : A 🡒 B ∈ Δ) (d : ⊢ᴳ[𝐆𝐋] insert A Γ ⟹ insert B Δ) :
    ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ :=
  Nonempty.map (.impR hAB) d

@[grind .] lemma boxGL (hΘ : Θ.box ⊆ Γ) (hA : □A ∈ Δ)
    (d : ⊢ᴳ[𝐆𝐋] insert (□A) (Θ ∪ Θ.box) ⟹ {A}) : ⊢ᴳ[𝐆𝐋] Γ ⟹ Δ :=
  Nonempty.map (.boxGL hΘ hA) d

@[elab_as_elim, induction_eliminator]
theorem rec {motive : (S : Sequent α) → ⊢ᴳ[𝐆𝐋] S → Prop}
    (axm : ∀ {Γ Δ A} (hΓ : A ∈ Γ) (hΔ : A ∈ Δ), motive (Γ ⟹ Δ) (.axm hΓ hΔ))
    (botL : ∀ {Γ Δ} (h : ⊥ ∈ Γ), motive (Γ ⟹ Δ) (.botL h))
    (impL : ∀ {Γ Δ A B} (hAB : A 🡒 B ∈ Γ) (d₁ : ⊢ᴳ[𝐆𝐋] Γ ⟹ insert A Δ)
      (d₂ : ⊢ᴳ[𝐆𝐋] insert B Γ ⟹ Δ), motive _ d₁ → motive _ d₂ → motive _ (.impL hAB d₁ d₂))
    (impR : ∀ {Γ Δ A B} (hAB : A 🡒 B ∈ Δ) (d : ⊢ᴳ[𝐆𝐋] insert A Γ ⟹ insert B Δ),
      motive _ d → motive _ (.impR hAB d))
    (boxGL : ∀ {Γ Δ Θ A} (hΘ : Θ.box ⊆ Γ) (hA : □A ∈ Δ)
      (d : ⊢ᴳ[𝐆𝐋] insert (□A) (Θ ∪ Θ.box) ⟹ {A}), motive _ d → motive _ (.boxGL hΘ hA d)) :
    ∀ {S} (h : ⊢ᴳ[𝐆𝐋] S), motive S h := by
  rintro S ⟨D⟩
  induction D with
  | axm hΓ hΔ => exact axm hΓ hΔ
  | botL h => exact botL h
  | impL hAB _ _ ih₁ ih₂ => exact impL hAB _ _ ih₁ ih₂
  | impR hAB _ ih => exact impR hAB _ ih
  | boxGL hΘ hA _ ih => exact boxGL hΘ hA _ ih

end logicGL.Derivable

end Modal

end
