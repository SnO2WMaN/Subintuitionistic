module

public import Subintuitionistic.Modal.Sequent
public import Mathlib.Data.Finset.Image

/-!
# The sequent calculus of `GL`

`⊢ᴳ[𝐆𝐋] Γ ⟹ Δ` states that the sequent `Γ ⟹ Δ` is derivable in a cut-free sequent calculus for
`GL` in the style of G3: initial sequents carry contexts and the principal formula of a rule
stays in its conclusion, so weakening and contraction are built in. The modal rule is

  `□A, Θ, □Θ ⟹ A`  infers  `□Θ, Γ ⟹ □A, Δ`.
-/

@[expose] public section

namespace Modal

namespace GL

variable {α : Type*} [DecidableEq α]

/-- The cut-free sequent calculus of `GL`.

- [SV82] -/
inductive Gentzen : Sequent α → Prop
  | axm {Γ Δ A} : A ∈ Γ → A ∈ Δ → Gentzen (Γ ⟹ Δ)
  | botL {Γ Δ} : ⊥ ∈ Γ → Gentzen (Γ ⟹ Δ)
  | impL {Γ Δ A B} :
    A 🡒 B ∈ Γ → Gentzen (Γ ⟹ insert A Δ) → Gentzen (insert B Γ ⟹ Δ) → Gentzen (Γ ⟹ Δ)
  | impR {Γ Δ A B} : A 🡒 B ∈ Δ → Gentzen (insert A Γ ⟹ insert B Δ) → Gentzen (Γ ⟹ Δ)
  | boxGL {Γ Δ Θ A} :
    Θ.image Formula.box ⊆ Γ → □A ∈ Δ →
    Gentzen (insert (□A) (Θ ∪ Θ.image Formula.box) ⟹ {A}) → Gentzen (Γ ⟹ Δ)

attribute [grind .] Gentzen.axm Gentzen.botL Gentzen.impL Gentzen.impR Gentzen.boxGL

end GL

@[inherit_doc] scoped[Modal] notation:45 "⊢ᴳ[𝐆𝐋] " S:50 => GL.Gentzen S
scoped[Modal] notation:45 "⊬ᴳ[𝐆𝐋] " S:50 => ¬GL.Gentzen S

end Modal

end
