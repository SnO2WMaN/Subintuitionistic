module

public import Subintuitionistic.Propositional.FPL.Kripke
public import Subintuitionistic.Modal.GL.Kripke
public import Subintuitionistic.Translation.Gödel
public import Subintuitionistic.Translation.Visser
public import Mathlib.Tactic.TFAE

/-!
# Embeddings of `FPL` into `GL`

`iff_gödel`, `iff_visser` and `mem_logicFPL_TFAE` embed `𝐅𝐏𝐋` into `𝐆𝐋` by `Aᵍ` and `Aᵛ`.

## References

- [Vis81, Theorem 5.4]
-/

@[expose] public section

namespace Propositional

open Modal

universe u

variable {α : Type u} [DecidableEq α] {Γ : FormulaFinset α} {A : Formula α}

namespace logicFPL.Derivable

/-- - [Vis81, Theorem 5.4] -/
theorem iff_gödel : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ {A} ↔ ⊢ᴳ[𝐆𝐋] Γᵍ ⟹ {Aᵍ} :=
  iff_valid.trans <| Translation.valid_iff_gödel.trans logicGL.Derivable.iff_valid.symm

/-- - [Vis81, Theorem 5.4] -/
theorem iff_visser : ⊢ᴳ[𝐅𝐏𝐋] Γ ⟹ {A} ↔ ⊢ᴳ[𝐆𝐋] Γᵛ ⟹ {Aᵛ} :=
  iff_valid.trans <| Translation.valid_iff_visser.trans logicGL.Derivable.iff_valid.symm

end logicFPL.Derivable

/-- - [Vis81, Theorem 5.4] -/
theorem mem_logicFPL_TFAE : [A ∈ 𝐅𝐏𝐋, Aᵍ ∈ 𝐆𝐋, Aᵛ ∈ 𝐆𝐋].TFAE := by
  tfae_have 1 ↔ 2 := by
    simpa [logicFPL, logicGL] using logicFPL.Derivable.iff_gödel (Γ := ∅) (A := A)
  tfae_have 1 ↔ 3 := by
    simpa [logicFPL, logicGL] using logicFPL.Derivable.iff_visser (Γ := ∅) (A := A)
  tfae_finish

end Propositional

end
