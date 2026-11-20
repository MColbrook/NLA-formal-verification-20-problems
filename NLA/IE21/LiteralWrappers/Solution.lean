module

public import NLA.IE21.LiteralWrappers.Slope
public import NLA.IE21.LiteralWrappers.Spherical

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal BigOperators RealInnerProductSpace
namespace NLA.IE21.LiteralWrappers.Interface
open NLA.IE21.QuantileIntegral

theorem trimDual_hasDerivAt {m : ℕ} (k : ℕ) (y : Fin m → ℝ) (t : ℝ)
    (ht : ∀ i, t ≠ y i) :
    HasDerivAt (trimDual k y)
      ((k : ℝ) / m - ((Finset.univ.filter (fun i => y i < t)).card : ℝ) / m) t := by
  exact NLA.IE21.LiteralWrappers.trimDual_hasDerivAt k y t ht

theorem trimDual_slope_signs {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (y : Fin m → ℝ) (t : ℝ)
    (ht : ∀ i, t ≠ y i) :
    ((Finset.univ.filter (fun i => y i < t)).card < k ↔ 0 < deriv (trimDual k y) t) ∧
    ((Finset.univ.filter (fun i => y i < t)).card = k ↔ deriv (trimDual k y) t = 0) ∧
    (k < (Finset.univ.filter (fun i => y i < t)).card ↔ deriv (trimDual k y) t < 0) := by
  exact NLA.IE21.LiteralWrappers.trimDual_slope_signs hm k y t ht

theorem actual_quantile_bounds {Ω : Type*} [instΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [probμ : IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hmean : ∫ ω, Y ω ∂μ = 1) [atomlessY : NullSingletonClass (μ.map Y)]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    let b := lowerQuantile (μ.map Y) θ
    0 < b ∧ b ≤ 1 / (1-θ) ∧ b ≤ truncationScale θ ∧
      μ.real {ω | Y ω ≤ b} = θ ∧
      populationTrim θ μ Y = ∫ ω, {ω | Y ω ≤ b}.indicator Y ω ∂μ := by
  exact NLA.IE21.LiteralWrappers.actual_quantile_bounds μ Y hYm hY hY0 hmean θ hθ

theorem mean_one_large_threshold_mass {Ω : Type*} [instΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [probμ : IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hmean : ∫ ω, Y ω ∂μ = 1) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    (1 + θ) / 2 ≤ μ.real {ω | Y ω ≤ truncationScale θ} := by
  exact NLA.IE21.LiteralWrappers.mean_one_large_threshold_mass μ Y hYm hY hY0 hmean θ hθ

theorem mean_one_trim_le_theta {Ω : Type*} [instΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [probμ : IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hmean : ∫ ω, Y ω ∂μ = 1) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    populationTrim θ μ Y ≤ θ := by
  exact NLA.IE21.LiteralWrappers.mean_one_trim_le_theta μ Y hY hY0 hmean θ hθ

theorem fixed_quantile_two_tails {Ω Ξ : Type*} [instΩ : MeasurableSpace Ω] [instΞ : MeasurableSpace Ξ]
    (μ : Measure Ξ) [probμ : IsProbabilityMeasure μ] (ν : Measure Ω) [probν : IsProbabilityMeasure ν]
    {m : ℕ} (hm : 1 ≤ m) (R : Fin m → Ω → Ξ)
    (hR : ∀ i, Measurable (R i)) (hind : iIndepFun R ν)
    (hlaw : ∀ i, ν.map (R i) = μ) (Y : Ξ → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y μ) (hY0 : ∀ z, 0 ≤ Y z)
    (hmean : ∫ z, Y z ∂μ = 1) [atomlessY : NullSingletonClass (μ.map Y)]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (ε : ℝ) (hε : 0 ≤ ε) :
    let b := lowerQuantile (μ.map Y) θ
    ν.real {ω |
      ε < |(∑ i, {z | Y z ≤ b}.indicator (fun z => (1 : ℝ)) (R i ω)) / m - θ| ∨
      b*ε < |(∑ i, {z | Y z ≤ b}.indicator Y (R i ω)) / m - populationTrim θ μ Y|} ≤
      4 * Real.exp (-2 * (m : ℝ) * ε^2) := by
  exact NLA.IE21.LiteralWrappers.fixed_quantile_two_tails μ ν hm R hR hind hlaw Y hYm hY hY0 hmean θ hθ ε hε

theorem large_threshold_count_tail {Ω Ξ : Type*} [instΩ : MeasurableSpace Ω] [instΞ : MeasurableSpace Ξ]
    (μ : Measure Ξ) [probμ : IsProbabilityMeasure μ] (ν : Measure Ω) [probν : IsProbabilityMeasure ν]
    {m : ℕ} (hm : 1 ≤ m) (R : Fin m → Ω → Ξ)
    (hR : ∀ i, Measurable (R i)) (hind : iIndepFun R ν)
    (hlaw : ∀ i, ν.map (R i) = μ) (Y : Ξ → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y μ) (hY0 : ∀ z, 0 ≤ Y z)
    (hmean : ∫ z, Y z ∂μ = 1) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ν.real {ω | (Finset.univ.filter (fun i => Y (R i ω) ≤ truncationScale θ)).card < retainedRows θ m} ≤
      Real.exp (-(m : ℝ)*(1-θ)^2/2) := by
  exact NLA.IE21.LiteralWrappers.large_threshold_count_tail μ ν hm R hR hind hlaw Y hYm hY hY0 hmean θ hθ

theorem indicator_trim_replacement {m : ℕ} (hm : 1 ≤ m)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (b L : ℝ) (hb : 0 ≤ b) (hbL : b ≤ L)
    (hcount : retainedRows θ m ≤ (Finset.univ.filter (fun i => y i ≤ L)).card)
    (P ε : ℝ) (hε : 0 ≤ ε)
    (hW : |(∑ i, if y i ≤ b then (1 : ℝ) else 0)/m-θ| ≤ ε)
    (hZ : |(∑ i, if y i ≤ b then y i else 0)/m-P| ≤ b*ε) :
    |(retainedRows θ m : ℝ) - ((Finset.univ.filter (fun i => y i ≤ b)).card : ℝ)| ≤ m*ε+1 ∧
    |finiteTrim (retainedRows θ m) y - (∑ i, if y i ≤ b then y i else 0)| ≤ L*(m*ε+1) ∧
    |finiteTrim (retainedRows θ m) y/m-P| ≤ 2*L*ε+L/m := by
  exact NLA.IE21.LiteralWrappers.indicator_trim_replacement hm θ hθ y hy b L hb hbL hcount P ε hε hW hZ

theorem zero_retained_shortcut {Ω : Type*} [instΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [probμ : IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω) (hmean : ∫ ω, Y ω ∂μ = 1)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (m : ℕ) (hm : 1 ≤ m) (hk : retainedRows θ m = 0) :
    populationTrim θ μ Y ≤ θ ∧ θ < 1/(m : ℝ) := by
  exact NLA.IE21.LiteralWrappers.zero_retained_shortcut μ Y hY hY0 hmean θ hθ m hm hk

theorem count_exponent_comparison (θ ε : ℝ) (hθ : θ < 1)
    (hε : 0 ≤ ε ∧ ε ≤ (1-θ)/2) (m : ℕ) :
    Real.exp (-(m : ℝ)*(1-θ)^2/2) ≤ Real.exp (-2*(m : ℝ)*ε^2) := by
  exact NLA.IE21.LiteralWrappers.count_exponent_comparison θ ε hθ hε m

theorem spherical_literal_concentration (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 2 ≤ n) (x : Space n) (hx : ‖x‖ = 1)
    (ε : ℝ) (hε : 0 < ε ∧ ε ≤ (1-θ)/2) :
    let Y := directionalEnergy x
    let b := lowerQuantile ((sphereLaw n).map Y) θ
    0 < b ∧ b ≤ 1/(1-θ) ∧ b ≤ truncationScale θ ∧
    (sphereLaw n).real {u | Y u ≤ b} = θ ∧
    populationTrim θ (sphereLaw n) Y = ∫ u, {v | Y v ≤ b}.indicator Y u ∂sphereLaw n ∧
    populationTrim θ (sphereLaw n) Y ≤ θ ∧
    (1+θ)/2 ≤ (sphereLaw n).real {u | Y u ≤ truncationScale θ} ∧
    (matrixLaw m n).real {A |
      ε < |(∑ i, {u | Y u ≤ b}.indicator (fun u => (1 : ℝ)) (matrixRow A i))/m-θ| ∨
      b*ε < |(∑ i, {u | Y u ≤ b}.indicator Y (matrixRow A i))/m-populationTrim θ (sphereLaw n) Y|} ≤
      4*Real.exp (-2*(m : ℝ)*ε^2) ∧
    (matrixLaw m n).real {A | (Finset.univ.filter (fun i => Y (matrixRow A i) ≤ truncationScale θ)).card < retainedRows θ m} ≤
      Real.exp (-(m : ℝ)*(1-θ)^2/2) ∧
    Real.exp (-(m : ℝ)*(1-θ)^2/2) ≤ Real.exp (-2*(m : ℝ)*ε^2) := by
  exact NLA.IE21.LiteralWrappers.spherical_literal_concentration θ hθ m n hm hn x hx ε hε

end NLA.IE21.LiteralWrappers.Interface
