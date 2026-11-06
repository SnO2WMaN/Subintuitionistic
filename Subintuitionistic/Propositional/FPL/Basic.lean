module

public import Subintuitionistic.Propositional.Sequent

/-!
# The sequent calculus of `𝐅𝐏𝐋`
-/

@[expose] public section

namespace Propositional

namespace logicFPL

open FormulaFinset (imps)

variable {α : Type*} [DecidableEq α]

/-- - [IKK01, Section 3] -/
inductive Derivation : Sequent α → Type _
  | axm (A) : Derivation ({A} ⟹ {A})
  | botL : Derivation ({⊥} ⟹ ∅)
  | wk {Γ Γ' Δ Δ'} : Derivation (Γ ⟹ Δ) → Γ ⊆ Γ' → Δ ⊆ Δ' → Derivation (Γ' ⟹ Δ')
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

open FormulaFinset (imps)

variable {α : Type*} [DecidableEq α] {Γ Γ' Δ Δ' Θ : FormulaFinset α} {A B : Formula α}
  {P : Finset (Formula α × Formula α)}

lemma axm (A : Formula α) : ⊢ᴳ[𝐅𝐏𝐋] {A} ⟹ {A} := ⟨.axm A⟩

lemma botL : ⊢ᴳ[𝐅𝐏𝐋] ({⊥} ⟹ ∅ : Sequent α) := ⟨.botL⟩

@[grind →] lemma wk (d : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐅𝐏𝐋] Γ' ⟹ Δ' :=
  Nonempty.map (.wk · hΓ hΔ) d

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
    (wk : ∀ {Γ Γ' Δ Δ'} (d : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ'),
      motive _ d → motive _ (d.wk hΓ hΔ))
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
  | wk _ hΓ hΔ ih => exact wk _ hΓ hΔ ih
  | andL _ ih => exact andL _ ih
  | andR _ _ ih₁ ih₂ => exact andR _ _ ih₁ ih₂
  | orL _ _ ih₁ ih₂ => exact orL _ _ ih₁ ih₂
  | orR _ ih => exact orR _ ih
  | impR _ ih => exact impR _ ih

@[grind →] lemma axm_mem (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ :=
  (axm A).wk (by simpa) (by simpa)

@[grind ←] lemma botL_mem (h : ⊥ ∈ Γ) : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ Δ := botL.wk (by simpa) (Finset.empty_subset _)

end logicFPL.Derivable

end Propositional

end
