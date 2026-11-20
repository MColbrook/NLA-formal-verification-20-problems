module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace NLA.IE21.ThresholdSelectors
variable {Ω : Type*} [MeasurableSpace Ω]

def thresholdWeight (Y : Ω → ℝ) (q c : ℝ) (ω : Ω) : ℝ :=
  if Y ω < q then 1 else if Y ω = q then c else 0

def Feasible (μ : Measure Ω) (θ : ℝ) (w : Ω → ℝ) : Prop :=
  Measurable w ∧ (∀ ω, 0 ≤ w ω ∧ w ω ≤ 1) ∧ (∫ ω, w ω ∂μ) = θ

def selectorCost (μ : Measure Ω) (Y w : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (Y ω * w ω) ∂μ

def primalTrim (θ : ℝ) (μ : Measure Ω) (Y : Ω → ℝ) : ℝ≥0∞ :=
  sInf {z | ∃ w : Ω → ℝ, Feasible μ θ w ∧ z = selectorCost μ Y w}

end NLA.IE21.ThresholdSelectors
