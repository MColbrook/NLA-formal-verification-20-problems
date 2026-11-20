module

public import NLA.IE21.Definitions
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace NLA.IE21.PrintedRate
def rate (m n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) / m * Real.log ((m : ℝ) / n)) +
    (Real.sqrt (n : ℝ))⁻¹ + (m : ℝ)⁻¹
def rateConstant (θ : ℝ) : ℝ := 512 * (1 + truncationScale θ)
end NLA.IE21.PrintedRate
