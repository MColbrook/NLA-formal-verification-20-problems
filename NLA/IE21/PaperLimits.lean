module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import NLA.IE21.FiniteSize

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace NLA.IE21.Paper

theorem ratio_error_dominates (θ : ℝ) (hθ : θ < 1) (m n : ℕ)
    (d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    d ≤ finiteRatioError θ m n d d d ∧
    trimmingError θ m d d d + Real.sqrt (2/(n : ℝ)) ≤ finiteRatioError θ m n d d d := by
  have hL : 0 ≤ truncationScale θ := by unfold truncationScale; positivity
  have hD : 0 ≤ trimmingError θ m d d d := by unfold trimmingError; positivity
  have hr : 0 ≤ Real.sqrt (2/(n : ℝ)) := Real.sqrt_nonneg _
  have hden : 0 < 1-d := by linarith
  constructor
  · unfold finiteRatioError
    apply (le_div_iff₀ hden).mpr
    nlinarith
  · unfold finiteRatioError
    apply (le_div_iff₀ hden).mpr
    nlinarith [mul_nonneg hd.le (add_nonneg hD hr)]

/-- One joint probability statement entails all three printed limits. -/
theorem spherical_joint_limit (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ)/n j) atTop atTop)
    (η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => (matrixLaw (m j) (n j)).real
      {A | ¬(|normalizedDeletion θ A-gaussianTrim θ| ≤ η ∧
        |normalizedOperator A-1| ≤ η ∧ |deletionRatio θ A-gaussianTrim θ| ≤ η)})
      atTop (𝓝 0) := by
  obtain ⟨hadm,hfail,herr⟩ := aspect_schedule θ hθ m n hm hn hnlim hQlim
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hfail
  filter_upwards [hadm,herr.eventually (gt_mem_nhds hη)] with j hj he
  let d := aspectParameter (m j) (n j)
  have hd : 0 < d := hj.2.1
  have hd1 : d < 1 := hj.2.2.1
  have hdom := ratio_error_dominates θ hθ.2 (m j) (n j) d hd hd1
  let : IsProbabilityMeasure (matrixLaw (m j) (n j)) :=
    (product_row_semantics (m j) (n j) (hn j)).1
  have hsub : {A : Mat (m j) (n j) | ¬(|normalizedDeletion θ A-gaussianTrim θ| ≤ η ∧
        |normalizedOperator A-1| ≤ η ∧ |deletionRatio θ A-gaussianTrim θ| ≤ η)} ⊆
      {A | ¬(0 < operatorNorm A ∧ |normalizedOperator A-1| ≤ d ∧
        |normalizedDeletion θ A-gaussianTrim θ| ≤ trimmingError θ (m j) d d d + Real.sqrt (2/(n j : ℝ)) ∧
        |deletionRatio θ A-gaussianTrim θ| ≤ finiteRatioError θ (m j) (n j) d d d)} := by
    intro A hbad hgood
    apply hbad
    exact ⟨hgood.2.2.1.trans (hdom.2.trans he.le),
      hgood.2.1.trans (hdom.1.trans he.le), hgood.2.2.2.trans he.le⟩
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (finite_size_bound θ hθ (m j) (n j) (hm j) hj.1 d d d ⟨hd,hd1⟩
      ⟨hd,hj.2.2.2⟩ ⟨hd,hd1⟩)

theorem original_joint_limit (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ)/n j) atTop atTop)
    (Ω : ℕ → Type*) [∀ j, MeasurableSpace (Ω j)]
    (μ : (j : ℕ) → Measure (Ω j)) [∀ j, IsProbabilityMeasure (μ j)]
    (A : (j : ℕ) → Ω j → Mat (m j) (n j))
    (hA : ∀ j, IndependentSphereRows (μ j) (A j)) (η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => (μ j).real
      {ω | ¬(|normalizedDeletion θ (A j ω)-gaussianTrim θ| ≤ η ∧
        |normalizedOperator (A j ω)-1| ≤ η ∧ |deletionRatio θ (A j ω)-gaussianTrim θ| ≤ η)})
      atTop (𝓝 0) := by
  have he (j : ℕ) : (μ j).real
      {ω | ¬(|normalizedDeletion θ (A j ω)-gaussianTrim θ| ≤ η ∧
        |normalizedOperator (A j ω)-1| ≤ η ∧ |deletionRatio θ (A j ω)-gaussianTrim θ| ≤ η)} =
      (matrixLaw (m j) (n j)).real
      {B | ¬(|normalizedDeletion θ B-gaussianTrim θ| ≤ η ∧
        |normalizedOperator B-1| ≤ η ∧ |deletionRatio θ B-gaussianTrim θ| ≤ η)} := by
    rw [← independent_row_transport (μ j) (A j) (hA j)]
    have hstats := statistics_measurable (m j) (n j) θ hθ (hn j)
    have hD : Measurable (normalizedDeletion (m := m j) (n := n j) θ) :=
      (hstats.1.pow_const 2).const_mul _
    have hO : Measurable (normalizedOperator (m := m j) (n := n j)) :=
      (hstats.2.1.pow_const 2).const_mul _
    have hs : MeasurableSet {B : Mat (m j) (n j) |
        ¬(|normalizedDeletion θ B-gaussianTrim θ| ≤ η ∧ |normalizedOperator B-1| ≤ η ∧
          |deletionRatio θ B-gaussianTrim θ| ≤ η)} := by
      have hDabs : Measurable (fun B : Mat (m j) (n j) =>
          |normalizedDeletion θ B - gaussianTrim θ|) := by
        simpa only [Real.norm_eq_abs] using (hD.sub_const (gaussianTrim θ)).norm
      have hOabs : Measurable (fun B : Mat (m j) (n j) =>
          |normalizedOperator B - 1|) := by
        simpa only [Real.norm_eq_abs] using (hO.sub_const (1 : ℝ)).norm
      have hRabs : Measurable (fun B : Mat (m j) (n j) =>
          |deletionRatio θ B - gaussianTrim θ|) := by
        simpa only [Real.norm_eq_abs] using (hstats.2.2.1.sub_const (gaussianTrim θ)).norm
      exact ((measurableSet_le hDabs measurable_const).inter
        ((measurableSet_le hOabs measurable_const).inter
          (measurableSet_le hRabs measurable_const))).compl
    exact (map_measureReal_apply (hA j).1 hs).symm
  simpa only [he] using spherical_joint_limit θ hθ m n hm hn hnlim hQlim η hη

#print axioms original_joint_limit
end NLA.IE21.Paper
