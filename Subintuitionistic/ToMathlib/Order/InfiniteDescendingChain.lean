module

public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Infinite descending chains
-/

@[expose] public section

/-- A sequence `s 0, s 1, …` with `R (s (n + 1)) (s n)` for all `n`. -/
structure InfiniteDescendingChain {κ : Type*} (R : κ → κ → Prop) where
  toFun : ℕ → κ
  rel_succ : ∀ n, R (toFun (n + 1)) (toFun n)

namespace InfiniteDescendingChain

variable {κ : Type*} {R : κ → κ → Prop}

/-- The chain `s` converges to `r`: `R r (s n)` for all `n`, and `R (s n) y` for all large enough
`n` whenever `R r y`. -/
structure ConvergesTo (s : InfiniteDescendingChain R) (r : κ) : Prop where
  rel : ∀ n, R r (s.toFun n)
  eventually_rel : ∀ y, R r y → ∀ᶠ n in Filter.atTop, R (s.toFun n) y

end InfiniteDescendingChain

end
