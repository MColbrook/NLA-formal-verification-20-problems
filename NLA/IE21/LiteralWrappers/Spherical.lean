module

public import NLA.IE21.LiteralWrappers.Assembly
public import NLA.IE21.SphericalContinuity.Atomlessness
public import NLA.IE21.RowLaw
public import NLA.IE21.SphericalMoments

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal RealInnerProductSpace
namespace NLA.IE21.LiteralWrappers
open QuantileIntegral

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
  have hn1 : 1 ≤ n := by omega
  let : IsProbabilityMeasure (sphereLaw n) := (surface_probability n hn1).2.2.2.1
  have hrows := product_row_semantics m n hn1
  let : IsProbabilityMeasure (matrixLaw m n) := hrows.1
  let : NullSingletonClass ((sphereLaw n).map (directionalEnergy x)) :=
    SphericalContinuity.directionalEnergy_atomless n hn x hx
  have hYm : Measurable (directionalEnergy x) := by unfold directionalEnergy; fun_prop
  have hYi := directionalEnergy_integrable n hn1 x hx
  have hY0 (u : Space n) : 0 ≤ directionalEnergy x u := by unfold directionalEnergy; positivity
  have hmean := directionalEnergy_mean n hn1 x hx
  have hq := actual_quantile_bounds (sphereLaw n) (directionalEnergy x) hYm hYi hY0 hmean θ hθ
  refine ⟨hq.1, hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2,
    mean_one_trim_le_theta _ _ hYi hY0 hmean θ hθ,
    mean_one_large_threshold_mass _ _ hYm hYi hY0 hmean θ hθ, ?_, ?_,
    count_exponent_comparison θ ε hθ.2 ⟨hε.1.le, hε.2⟩ m⟩
  · exact fixed_quantile_two_tails (sphereLaw n) (matrixLaw m n) hm
      (fun i A => matrixRow A i) (measurable_matrixRow m n) hrows.2.1.2.1 hrows.2.1.2.2
      (directionalEnergy x) hYm hYi hY0 hmean θ hθ ε hε.1.le
  · exact large_threshold_count_tail (sphereLaw n) (matrixLaw m n) hm
      (fun i A => matrixRow A i) (measurable_matrixRow m n) hrows.2.1.2.1 hrows.2.1.2.2
      (directionalEnergy x) hYm hYi hY0 hmean θ hθ

#print axioms spherical_literal_concentration
end NLA.IE21.LiteralWrappers
