module

public import Subintuitionistic.Propositional.Sequent
public import Subintuitionistic.Propositional.FPL.Basic

/-!
# The sequent calculus of `DPL`, and the logics `SPL` and `DPL`

`logicDPL.Derivation` is a calculus on layered sequents with levels `0`, `1`, `2`; the levels `0`
and `1` alone are the calculus of `SPL`. `𝐒𝐏𝐋` and `𝐃𝐏𝐋` are given by derivability at level `1`
and `2`.
-/

@[expose] public section

namespace Propositional

namespace logicDPL

open logicFPL (imps)

variable {α : Type*} [DecidableEq α]

/-- - [Nog26, Definitions 4.2, 7.1] -/
inductive Derivation : LayeredSequent α → Type _
  | axm (ℓ) (a : α) : Derivation ({#a} ⟹[ℓ] {#a})
  | botL (ℓ) : Derivation ({⊥} ⟹[ℓ] ∅)
  | wk {ℓ Γ Γ' Δ Δ'} : Derivation (Γ ⟹[ℓ] Δ) → Γ ⊆ Γ' → Δ ⊆ Δ' → Derivation (Γ' ⟹[ℓ] Δ')
  | andL {ℓ Γ Δ A B} :
    Derivation (insert A (insert B Γ) ⟹[ℓ] Δ) → Derivation (insert (A ⋏ B) Γ ⟹[ℓ] Δ)
  | andR {ℓ Γ Δ A B} :
    Derivation (Γ ⟹[ℓ] insert A Δ) → Derivation (Γ ⟹[ℓ] insert B Δ) →
      Derivation (Γ ⟹[ℓ] insert (A ⋏ B) Δ)
  | orL {ℓ Γ Δ A B} :
    Derivation (insert A Γ ⟹[ℓ] Δ) → Derivation (insert B Γ ⟹[ℓ] Δ) →
      Derivation (insert (A ⋎ B) Γ ⟹[ℓ] Δ)
  | orR {ℓ Γ Δ A B} :
    Derivation (Γ ⟹[ℓ] insert A (insert B Δ)) → Derivation (Γ ⟹[ℓ] insert (A ⋎ B) Δ)
  | impL {Γ Δ A B} :
    Derivation (Γ ⟹[1] insert A Δ) → Derivation (insert B Γ ⟹[1] Δ) →
      Derivation (insert (A 🡒 B) Γ ⟹[1] Δ)
  | impR {Θ P A B} :
    (∀ I ⊆ P, Derivation (insert (A 🡒 B) (insert A (Θ ∪ I.image Prod.snd)) ⟹[0]
      insert B ((P \ I).image Prod.fst))) →
    Derivation (Θ ∪ imps P ⟹[0] {A 🡒 B})
  | liftUp₀₁ {Γ Δ} : Derivation (Γ ⟹[0] Δ) → Derivation (Γ ⟹[1] Δ)
  | liftUp₁₂ {P Q : Finset (Formula α × Formula α)} {Φ : Finset α} :
    Derivation (imps P ∪ Φ.image (#·) ⟹[1] imps Q) →
      Derivation (imps P ∪ Φ.image (#·) ⟹[2] imps Q)

/-- - [Nog26, Definitions 4.2, 7.1] -/
def Derivable (S : LayeredSequent α) : Prop := Nonempty (Derivation S)

end logicDPL

@[inherit_doc] scoped[Propositional] notation:45 "⊢ᴳ[𝐃𝐏𝐋]! " S:50 => logicDPL.Derivation S
@[inherit_doc] scoped[Propositional] notation:45 "⊢ᴳ[𝐃𝐏𝐋] " S:50 => logicDPL.Derivable S
scoped[Propositional] notation:45 "⊬ᴳ[𝐃𝐏𝐋] " S:50 => ¬logicDPL.Derivable S

variable {α : Type*} [DecidableEq α]

/-- - [Nog26, Definition 4.2] -/
def logicSPL : Logic α := {A | ⊢ᴳ[𝐃𝐏𝐋] ∅ ⟹[1] {A}}

/-- - [Nog26, Definition 7.1] -/
def logicDPL : Logic α := {A | ⊢ᴳ[𝐃𝐏𝐋] ∅ ⟹[2] {A}}

@[inherit_doc] scoped[Propositional] notation "𝐒𝐏𝐋" => logicSPL
@[inherit_doc] scoped[Propositional] notation "𝐃𝐏𝐋" => logicDPL

namespace logicDPL.Derivable

open logicFPL (imps)

variable {ℓ : Fin 3} {Γ Γ' Δ Δ' Θ : FormulaFinset α} {A B : Formula α}
  {P Q : Finset (Formula α × Formula α)} {Φ : Finset α}

lemma axm (ℓ : Fin 3) (a : α) : ⊢ᴳ[𝐃𝐏𝐋] {#a} ⟹[ℓ] {#a} := ⟨.axm ℓ a⟩

lemma botL (ℓ : Fin 3) : ⊢ᴳ[𝐃𝐏𝐋] ({⊥} ⟹[ℓ] ∅ : LayeredSequent α) := ⟨.botL ℓ⟩

lemma wk (d : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ') : ⊢ᴳ[𝐃𝐏𝐋] Γ' ⟹[ℓ] Δ' :=
  Nonempty.map (.wk · hΓ hΔ) d

lemma andL (d : ⊢ᴳ[𝐃𝐏𝐋] insert A (insert B Γ) ⟹[ℓ] Δ) : ⊢ᴳ[𝐃𝐏𝐋] insert (A ⋏ B) Γ ⟹[ℓ] Δ :=
  Nonempty.map .andL d

lemma andR (d₁ : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert A Δ) (d₂ : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert B Δ) :
    ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert (A ⋏ B) Δ :=
  Nonempty.map2 .andR d₁ d₂

lemma orL (d₁ : ⊢ᴳ[𝐃𝐏𝐋] insert A Γ ⟹[ℓ] Δ) (d₂ : ⊢ᴳ[𝐃𝐏𝐋] insert B Γ ⟹[ℓ] Δ) :
    ⊢ᴳ[𝐃𝐏𝐋] insert (A ⋎ B) Γ ⟹[ℓ] Δ :=
  Nonempty.map2 .orL d₁ d₂

lemma orR (d : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert A (insert B Δ)) : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert (A ⋎ B) Δ :=
  Nonempty.map .orR d

lemma impL (d₁ : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[1] insert A Δ) (d₂ : ⊢ᴳ[𝐃𝐏𝐋] insert B Γ ⟹[1] Δ) :
    ⊢ᴳ[𝐃𝐏𝐋] insert (A 🡒 B) Γ ⟹[1] Δ :=
  Nonempty.map2 .impL d₁ d₂

lemma impR
    (d : ∀ I ⊆ P, ⊢ᴳ[𝐃𝐏𝐋] insert (A 🡒 B) (insert A (Θ ∪ I.image Prod.snd)) ⟹[0]
      insert B ((P \ I).image Prod.fst)) :
    ⊢ᴳ[𝐃𝐏𝐋] Θ ∪ imps P ⟹[0] {A 🡒 B} :=
  ⟨.impR fun I hI ↦ (d I hI).some⟩

lemma liftUp₀₁ (d : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[0] Δ) : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[1] Δ := Nonempty.map .liftUp₀₁ d

lemma liftUp₁₂ (d : ⊢ᴳ[𝐃𝐏𝐋] imps P ∪ Φ.image (#·) ⟹[1] imps Q) :
    ⊢ᴳ[𝐃𝐏𝐋] imps P ∪ Φ.image (#·) ⟹[2] imps Q :=
  Nonempty.map .liftUp₁₂ d

@[elab_as_elim, induction_eliminator]
theorem rec {motive : (S : LayeredSequent α) → ⊢ᴳ[𝐃𝐏𝐋] S → Prop}
    (axm : ∀ ℓ a, motive _ (axm ℓ a)) (botL : ∀ ℓ, motive _ (botL ℓ))
    (wk : ∀ {ℓ Γ Γ' Δ Δ'} (d : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ) (hΓ : Γ ⊆ Γ') (hΔ : Δ ⊆ Δ'),
      motive _ d → motive _ (d.wk hΓ hΔ))
    (andL : ∀ {ℓ Γ Δ A B} (d : ⊢ᴳ[𝐃𝐏𝐋] insert A (insert B Γ) ⟹[ℓ] Δ),
      motive _ d → motive _ d.andL)
    (andR : ∀ {ℓ Γ Δ A B} (d₁ : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert A Δ) (d₂ : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert B Δ),
      motive _ d₁ → motive _ d₂ → motive _ (andR d₁ d₂))
    (orL : ∀ {ℓ Γ Δ A B} (d₁ : ⊢ᴳ[𝐃𝐏𝐋] insert A Γ ⟹[ℓ] Δ) (d₂ : ⊢ᴳ[𝐃𝐏𝐋] insert B Γ ⟹[ℓ] Δ),
      motive _ d₁ → motive _ d₂ → motive _ (orL d₁ d₂))
    (orR : ∀ {ℓ Γ Δ A B} (d : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert A (insert B Δ)),
      motive _ d → motive _ d.orR)
    (impL : ∀ {Γ Δ A B} (d₁ : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[1] insert A Δ) (d₂ : ⊢ᴳ[𝐃𝐏𝐋] insert B Γ ⟹[1] Δ),
      motive _ d₁ → motive _ d₂ → motive _ (impL d₁ d₂))
    (impR : ∀ {Θ A B} {P : Finset (Formula α × Formula α)}
      (d : ∀ I ⊆ P, ⊢ᴳ[𝐃𝐏𝐋] insert (A 🡒 B) (insert A (Θ ∪ I.image Prod.snd)) ⟹[0]
        insert B ((P \ I).image Prod.fst)),
      (∀ I hI, motive _ (d I hI)) → motive _ (impR d))
    (liftUp₀₁ : ∀ {Γ Δ} (d : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[0] Δ), motive _ d → motive _ d.liftUp₀₁)
    (liftUp₁₂ : ∀ {P Q : Finset (Formula α × Formula α)} {Φ : Finset α}
      (d : ⊢ᴳ[𝐃𝐏𝐋] imps P ∪ Φ.image (#·) ⟹[1] imps Q), motive _ d → motive _ d.liftUp₁₂) :
    ∀ {S} (h : ⊢ᴳ[𝐃𝐏𝐋] S), motive S h := by
  rintro S ⟨D⟩
  induction D with
  | axm ℓ a => exact axm ℓ a
  | botL ℓ => exact botL ℓ
  | wk _ hΓ hΔ ih => exact wk _ hΓ hΔ ih
  | andL _ ih => exact andL _ ih
  | andR _ _ ih₁ ih₂ => exact andR _ _ ih₁ ih₂
  | orL _ _ ih₁ ih₂ => exact orL _ _ ih₁ ih₂
  | orR _ ih => exact orR _ ih
  | impL _ _ ih₁ ih₂ => exact impL _ _ ih₁ ih₂
  | impR _ ih => exact impR _ ih
  | liftUp₀₁ _ ih => exact liftUp₀₁ _ ih
  | liftUp₁₂ _ ih => exact liftUp₁₂ _ ih

lemma union (hΓ : A ∈ Γ) (hΔ : A ∈ Δ) (hA : ∃ a, A = #a) : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ := by
  obtain ⟨a, rfl⟩ := hA
  exact wk (axm ℓ a) (by simpa) (by simpa)

lemma botL_mem (h : ⊥ ∈ Γ) : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ :=
  wk (botL ℓ) (by simpa) (Finset.empty_subset _)

lemma andL_of_mem (hAB : A ⋏ B ∈ Γ) (d : ⊢ᴳ[𝐃𝐏𝐋] insert A (insert B Γ) ⟹[ℓ] Δ) :
    ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ :=
  d.andL.wk (Finset.insert_subset hAB subset_rfl) subset_rfl

lemma andR_of_mem (hAB : A ⋏ B ∈ Δ) (d₁ : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert A Δ)
    (d₂ : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert B Δ) : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ :=
  (andR d₁ d₂).wk subset_rfl (Finset.insert_subset hAB subset_rfl)

lemma orL_of_mem (hAB : A ⋎ B ∈ Γ) (d₁ : ⊢ᴳ[𝐃𝐏𝐋] insert A Γ ⟹[ℓ] Δ)
    (d₂ : ⊢ᴳ[𝐃𝐏𝐋] insert B Γ ⟹[ℓ] Δ) : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ :=
  (orL d₁ d₂).wk (Finset.insert_subset hAB subset_rfl) subset_rfl

lemma orR_of_mem (hAB : A ⋎ B ∈ Δ) (d : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] insert A (insert B Δ)) :
    ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[ℓ] Δ :=
  d.orR.wk subset_rfl (Finset.insert_subset hAB subset_rfl)

lemma impL_of_mem (hAB : A 🡒 B ∈ Γ) (d₁ : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[1] insert A Δ)
    (d₂ : ⊢ᴳ[𝐃𝐏𝐋] insert B Γ ⟹[1] Δ) : ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[1] Δ :=
  (impL d₁ d₂).wk (Finset.insert_subset hAB subset_rfl) subset_rfl

lemma impR_of_mem (hP : imps P ⊆ Γ) (hAB : A 🡒 B ∈ Δ)
    (d : ∀ I ⊆ P, ⊢ᴳ[𝐃𝐏𝐋] insert (A 🡒 B) (insert A (Γ ∪ I.image Prod.snd)) ⟹[0]
      insert B ((P \ I).image Prod.fst)) :
    ⊢ᴳ[𝐃𝐏𝐋] Γ ⟹[0] Δ :=
  (impR d).wk (Finset.union_subset subset_rfl hP) (Finset.singleton_subset_iff.mpr hAB)

end logicDPL.Derivable

end Propositional

end
