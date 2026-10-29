module

public import Subintuitionistic.Propositional.Sequent
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Finset.Prod

/-!
# The sequent calculus of `FPL`

`logicFPL.Derivation` has a single rule for `🡒`, `impR`: the implications `imps P` of a finite set
`P` of pairs have one premise for each subset `I ⊆ P`. The occurrence of `A 🡒 B` in the
antecedent of the premises is Löb's rule.
-/

@[expose] public section

namespace Propositional

namespace logicFPL

variable {α : Type*} [DecidableEq α]

def imps (P : Finset (Formula α × Formula α)) : FormulaFinset α := P.image fun p ↦ p.1 🡒 p.2

@[grind ←] lemma mem_imps_of_mem {A B : Formula α} {P : Finset (Formula α × Formula α)}
    (h : (A, B) ∈ P) : A 🡒 B ∈ imps P :=
  Finset.mem_image_of_mem _ h

lemma exists_imps (Γ : FormulaFinset α) :
    ∃ P : Finset (Formula α × Formula α), imps P ⊆ Γ ∧ ∀ A B, A 🡒 B ∈ Γ → (A, B) ∈ P := by
  have hf : Function.Injective fun p : Formula α × Formula α ↦ p.1 🡒 p.2 :=
    fun p q hpq ↦ by grind
  exact ⟨Γ.preimage _ hf.injOn, fun x ↦ by grind [imps, Finset.mem_preimage], by simp⟩

/-- - [IKK01, Section 3] -/
inductive Derivation : Sequent α → Type _
  | axm (A) : Derivation ({A} ⟹ {A})
  | botL : Derivation ({⊥} ⟹ ∅)
  | wkL {Γ Γ' Δ} : Derivation (Γ ⟹ Δ) → Γ ⊆ Γ' → Derivation (Γ' ⟹ Δ)
  | wkR {Γ Δ Δ'} : Derivation (Γ ⟹ Δ) → Δ ⊆ Δ' → Derivation (Γ ⟹ Δ')
  | andL {Γ Δ A B} : Derivation (insert A (insert B Γ) ⟹ Δ) → Derivation (insert (A ⋏ B) Γ ⟹ Δ)
  | andR {Γ Δ A B} :
    Derivation (Γ ⟹ insert A Δ) → Derivation (Γ ⟹ insert B Δ) →
      Derivation (Γ ⟹ insert (A ⋏ B) Δ)
  | orL {Γ Δ A B} :
    Derivation (insert A Γ ⟹ Δ) → Derivation (insert B Γ ⟹ Δ) →
      Derivation (insert (A ⋎ B) Γ ⟹ Δ)
  | orR {Γ Δ A B} : Derivation (Γ ⟹ insert A (insert B Δ)) → Derivation (Γ ⟹ insert (A ⋎ B) Δ)
  | impR {Θ P A B} :
    (∀ I ⊆ P, Derivation (insert (A 🡒 B) (insert A (Θ ∪ I.image Prod.snd)) ⟹
      insert B ((P \ I).image Prod.fst))) →
    Derivation (Θ ∪ imps P ⟹ {A 🡒 B})

/-- - [IKK01, Section 3] -/
def Derivable (S : Sequent α) : Prop := Nonempty (Derivation S)

end logicFPL

@[inherit_doc] scoped[Propositional] notation:45 "⊢ᴳ[𝐅𝐏𝐋]! " S:50 => logicFPL.Derivation S
@[inherit_doc] scoped[Propositional] notation:45 "⊢ᴳ[𝐅𝐏𝐋] " S:50 => logicFPL.Derivable S
scoped[Propositional] notation:45 "⊬ᴳ[𝐅𝐏𝐋] " S:50 => ¬logicFPL.Derivable S

section

variable {α : Type*} [DecidableEq α]

/-- - [IKK01, Section 3] -/
def logicFPL : Logic α := {A | ⊢ᴳ[𝐅𝐏𝐋] ∅ ⟹ {A}}

@[inherit_doc] scoped[Propositional] notation "𝐅𝐏𝐋" => logicFPL

end

namespace logicFPL.Derivable

variable {α : Type*} [DecidableEq α] {Γ Γ' Δ Δ' Θ : FormulaFinset α} {A B : Formula α}
  {P : Finset (Formula α × Formula α)}

lemma axm (A : Formula α) : ⊢ᴳ[𝐅𝐏𝐋] {A} ⟹ {A} := ⟨.axm A⟩

lemma botL : ⊢ᴳ[𝐅𝐏𝐋] ({⊥} ⟹ ∅ : Sequent α) := ⟨.botL⟩

lemma wkL (d : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') : ⊢ᴳ[𝐅𝐏𝐋] Γ' ⟹ Δ := Nonempty.map (.wkL · hΓ) d

lemma wkR (d : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ) (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ' := Nonempty.map (.wkR · hΔ) d

lemma andL (d : ⊢ᴳ[𝐅𝐏𝐋] insert A (insert B Γ) ⟹ Δ) : ⊢ᴳ[𝐅𝐏𝐋] insert (A ⋏ B) Γ ⟹ Δ :=
  Nonempty.map .andL d

lemma andR (d₁ : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ insert A Δ) (d₂ : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ insert B Δ) :
    ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ insert (A ⋏ B) Δ :=
  Nonempty.map2 .andR d₁ d₂

lemma orL (d₁ : ⊢ᴳ[𝐅𝐏𝐋] insert A Γ ⟹ Δ) (d₂ : ⊢ᴳ[𝐅𝐏𝐋] insert B Γ ⟹ Δ) :
    ⊢ᴳ[𝐅𝐏𝐋] insert (A ⋎ B) Γ ⟹ Δ :=
  Nonempty.map2 .orL d₁ d₂

lemma orR (d : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ insert A (insert B Δ)) : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ insert (A ⋎ B) Δ :=
  Nonempty.map .orR d

lemma impR
    (d : ∀ I ⊆ P, ⊢ᴳ[𝐅𝐏𝐋] insert (A 🡒 B) (insert A (Θ ∪ I.image Prod.snd)) ⟹
      insert B ((P \ I).image Prod.fst)) :
    ⊢ᴳ[𝐅𝐏𝐋] Θ ∪ imps P ⟹ {A 🡒 B} :=
  ⟨.impR fun I hI ↦ (d I hI).some⟩

@[elab_as_elim, induction_eliminator]
theorem rec {motive : (S : Sequent α) → ⊢ᴳ[𝐅𝐏𝐋] S → Prop}
    (axm : ∀ A, motive _ (axm A)) (botL : motive _ botL)
    (wkL : ∀ {Γ Γ' Δ} (d : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ'), motive _ d → motive _ (d.wkL hΓ))
    (wkR : ∀ {Γ Δ Δ'} (d : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ) (hΔ : Δ ⊆ Δ'), motive _ d → motive _ (d.wkR hΔ))
    (andL : ∀ {Γ Δ A B} (d : ⊢ᴳ[𝐅𝐏𝐋] insert A (insert B Γ) ⟹ Δ), motive _ d → motive _ d.andL)
    (andR : ∀ {Γ Δ A B} (d₁ : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ insert A Δ) (d₂ : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ insert B Δ),
      motive _ d₁ → motive _ d₂ → motive _ (andR d₁ d₂))
    (orL : ∀ {Γ Δ A B} (d₁ : ⊢ᴳ[𝐅𝐏𝐋] insert A Γ ⟹ Δ) (d₂ : ⊢ᴳ[𝐅𝐏𝐋] insert B Γ ⟹ Δ),
      motive _ d₁ → motive _ d₂ → motive _ (orL d₁ d₂))
    (orR : ∀ {Γ Δ A B} (d : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ insert A (insert B Δ)), motive _ d → motive _ d.orR)
    (impR : ∀ {Θ A B} {P : Finset (Formula α × Formula α)}
      (d : ∀ I ⊆ P, ⊢ᴳ[𝐅𝐏𝐋] insert (A 🡒 B) (insert A (Θ ∪ I.image Prod.snd)) ⟹
        insert B ((P \ I).image Prod.fst)),
      (∀ I hI, motive _ (d I hI)) → motive _ (impR d)) :
    ∀ {S} (h : ⊢ᴳ[𝐅𝐏𝐋] S), motive S h := by
  rintro S ⟨D⟩
  induction D with
  | axm A => exact axm A
  | botL => exact botL
  | wkL _ hΓ ih => exact wkL _ hΓ ih
  | wkR _ hΔ ih => exact wkR _ hΔ ih
  | andL _ ih => exact andL _ ih
  | andR _ _ ih₁ ih₂ => exact andR _ _ ih₁ ih₂
  | orL _ _ ih₁ ih₂ => exact orL _ _ ih₁ ih₂
  | orR _ ih => exact orR _ ih
  | impR _ ih => exact impR _ ih

@[grind →] lemma wk (h : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐅𝐏𝐋] Γ' ⟹ Δ' :=
  wkR (wkL h hΓ) hΔ

@[grind →] lemma union (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ := (axm A).wk (by simpa) (by simpa)

@[grind ←] lemma botL_mem (h : ⊥ ∈ Γ) : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ := botL.wk (by simpa) (Finset.empty_subset _)

end logicFPL.Derivable

end Propositional

end
