module

public import NLA.IE21.PrintedRate.Proof

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set NLA.IE21.PrintedRate
open scoped Topology

namespace NLA.IE21.PrintedJointRate

theorem actual_finite_normalized_rate_error (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (ht : aspectParameter m n ≤ 1/2) :
    trimmingError θ m (aspectParameter m n) (aspectParameter m n)
      (aspectParameter m n) + Real.sqrt (2 / (n : ℝ)) ≤
      rateConstant θ * rate m n := by
  have hL : 0 ≤ truncationScale θ := by
    unfold truncationScale
    exact div_nonneg (by norm_num) (sub_pos.mpr hθ.2).le
  have ht0 : 0 ≤ aspectParameter m n := by unfold aspectParameter; positivity
  have he0 : 0 ≤ trimmingError θ m (aspectParameter m n)
      (aspectParameter m n) (aspectParameter m n) := by
    unfold trimmingError
    positivity
  have hd : 0 < 1 - aspectParameter m n := by linarith
  have he : trimmingError θ m (aspectParameter m n) (aspectParameter m n)
      (aspectParameter m n) + Real.sqrt (2 / (n : ℝ)) ≤
      finiteRatioError θ m n (aspectParameter m n) (aspectParameter m n)
        (aspectParameter m n) := by
    unfold finiteRatioError
    apply (le_div_iff₀ hd).mpr
    nlinarith [mul_nonneg he0 ht0, mul_nonneg (Real.sqrt_nonneg (2 / (n : ℝ))) ht0]
  exact he.trans (PrintedRate.actual_finite_rate_error θ hθ m n hm hn ht)

/-- The same literal rate holds jointly for the normalized trimmed squared
singular value and its ratio to the largest squared singular value. -/
theorem actual_joint_rate_probability_limit (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    Tendsto (fun j => (matrixLaw (m j) (n j)).real
      {A | |normalizedDeletion θ A - gaussianTrim θ| >
          rateConstant θ * rate (m j) (n j) ∨
        |deletionRatio θ A - gaussianTrim θ| >
          rateConstant θ * rate (m j) (n j)}) atTop (𝓝 0) := by
  obtain ⟨hadm, hfail, _⟩ := aspect_schedule θ hθ m n hm hn hnlim hQlim
  have hhalf := (aspectParameter_tendsto_zero m n hQlim).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  apply squeeze_zero' (Eventually.of_forall (fun j => measureReal_nonneg)) _ hfail
  filter_upwards [hadm, hhalf] with j hj hhalfj
  let d := aspectParameter (m j) (n j)
  let : IsProbabilityMeasure (matrixLaw (m j) (n j)) :=
    (product_row_semantics (m j) (n j) (hn j)).1
  have hnorm := actual_finite_normalized_rate_error θ hθ (m j) (n j) (hm j) (hn j) hhalfj.le
  have hratio := PrintedRate.actual_finite_rate_error θ hθ (m j) (n j) (hm j) (hn j) hhalfj.le
  have hs : {A : Mat (m j) (n j) | |normalizedDeletion θ A - gaussianTrim θ| >
          rateConstant θ * rate (m j) (n j) ∨
        |deletionRatio θ A - gaussianTrim θ| > rateConstant θ * rate (m j) (n j)} ⊆
      {A | ¬(0 < operatorNorm A ∧ |normalizedOperator A - 1| ≤ d ∧
        |normalizedDeletion θ A - gaussianTrim θ| ≤
          trimmingError θ (m j) d d d + Real.sqrt (2 / (n j : ℝ)) ∧
        |deletionRatio θ A - gaussianTrim θ| ≤ finiteRatioError θ (m j) (n j) d d d)} := by
    intro A hA hgood
    rcases hA with hA | hA
    · exact (not_lt_of_ge (hgood.2.2.1.trans hnorm)) hA
    · exact (not_lt_of_ge (hgood.2.2.2.trans hratio)) hA
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    (finite_size_bound θ hθ (m j) (n j) (hm j) hj.1 d d d
      ⟨hj.2.1, hj.2.2.1⟩ ⟨hj.2.1, hj.2.2.2⟩ ⟨hj.2.1, hj.2.2.1⟩)

#print axioms actual_finite_normalized_rate_error
#print axioms actual_joint_rate_probability_limit

end NLA.IE21.PrintedJointRate
