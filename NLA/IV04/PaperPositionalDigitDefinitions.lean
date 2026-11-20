module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction

/-- Literal little-endian base-b value; no decoding correctness is assumed. -/
def positionalValue (b : ℕ) {n : ℕ} (d : Fin n → ℕ) : ℕ :=
  ∑ i, d i * b^i.val

end IV04.Paper.Computational.SATReduction