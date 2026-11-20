module

public import NLA.RA02.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- The literal diagonal perturbation and normalization in rap-prop:correlation. -/
def regularizedCorrelation {n : ℕ} (C : NLA.RA02.Square n) (δ : ℝ) : NLA.RA02.Square n :=
  ((1+δ)⁻¹ : ℝ) • (C+(δ : ℝ) • (1 : NLA.RA02.Square n))

end NLA.RA02.Paper
