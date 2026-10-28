module

public import Subintuitionistic.Propositional.FPL.Kripke
public import Subintuitionistic.Modal.GL.Kripke
public import Subintuitionistic.Translation.Gödel
public import Subintuitionistic.Translation.Visser
public import Mathlib.Tactic.TFAE

/-!
# Embeddings of `FPL` into `GL`

`Γ ⟹ {A}` is derivable in `FPL` if and only if `Γᵍ ⟹ {Aᵍ}` is derivable in `GL`, and if and only
if `Γᵛ ⟹ {Aᵛ}` is; in particular, `A` is a theorem of `FPL` if and only if `Aᵍ` is a theorem of
`GL`, and if and only if `Aᵛ` is.

## References

- [Vis81, Theorem 5.4]
-/

@[expose] public section

namespace Translation

open Propositional Modal

universe u

variable {α : Type u} [DecidableEq α] {Γ : Propositional.FormulaFinset α}
  {A : Propositional.Formula α}

/-- `Γ ⟹ {A}` is derivable in `FPL` if and only if `Γᵍ ⟹ {Aᵍ}` is derivable in `GL`.
- [Vis81, Theorem 5.4] -/
theorem gentzen_iff_gödel : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ {A} ↔ ⊢ᴳ[𝐆𝐋] Γᵍ ⟹ {Aᵍ} :=
  FPL.Gentzen.iff_valid.trans <| valid_iff_gödel.trans GL.Gentzen.iff_valid.symm

/-- `Γ ⟹ {A}` is derivable in `FPL` if and only if `Γᵛ ⟹ {Aᵛ}` is derivable in `GL`.
- [Vis81, Theorem 5.4] -/
theorem gentzen_iff_visser : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ {A} ↔ ⊢ᴳ[𝐆𝐋] Γᵛ ⟹ {Aᵛ} :=
  FPL.Gentzen.iff_valid.trans <| valid_iff_visser.trans GL.Gentzen.iff_valid.symm

/-- `A` is a theorem of `FPL` if and only if `Aᵍ` is a theorem of `GL`, and if and only if `Aᵛ`
is.
- [Vis81, Theorem 5.4] -/
theorem theorem_TFAE : [⊢ᴳ[𝐅𝐏𝐋] ∅ ⟹ {A}, ⊢ᴳ[𝐆𝐋] ∅ ⟹ {Aᵍ}, ⊢ᴳ[𝐆𝐋] ∅ ⟹ {Aᵛ}].TFAE := by
  tfae_have 1 ↔ 2 := by simpa using gentzen_iff_gödel (Γ := ∅) (A := A)
  tfae_have 1 ↔ 3 := by simpa using gentzen_iff_visser (Γ := ∅) (A := A)
  tfae_finish

end Translation

end
