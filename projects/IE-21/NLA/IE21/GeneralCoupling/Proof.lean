module

public import NLA.IE21.GeneralCoupling.Definitions
public import NLA.IE21.ThresholdSelectors.Duality

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology
namespace NLA.IE21.GeneralCoupling
open ThresholdSelectors
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y Z w : Ω → ℝ} {θ : ℝ}

theorem couplingDistance_symm : couplingDistance μ Y Z = couplingDistance μ Z Y := by
  unfold couplingDistance
  simp_rw [abs_sub_comm (Y _) (Z _)]

theorem selectorCost_le_add_couplingDistance (hZ : Measurable Z)
    (hw : Feasible μ θ w) :
    selectorCost μ Y w ≤ selectorCost μ Z w + couplingDistance μ Y Z := by
  have hp (ω : Ω) : Y ω * w ω ≤ Z ω * w ω + |Y ω - Z ω| := by
    have hb := hw.2.1 ω
    have h1 := mul_le_mul_of_nonneg_right (le_abs_self (Y ω - Z ω)) hb.1
    have h2 := mul_le_mul_of_nonneg_left hb.2 (abs_nonneg (Y ω - Z ω))
    nlinarith
  calc
    selectorCost μ Y w ≤ ∫⁻ ω, ENNReal.ofReal (Z ω * w ω) + ENNReal.ofReal |Y ω - Z ω| ∂μ := by
      apply lintegral_mono
      intro ω
      exact (ENNReal.ofReal_le_ofReal (hp ω)).trans ENNReal.ofReal_add_le
    _ = selectorCost μ Z w + couplingDistance μ Y Z :=
      lintegral_add_left ((hZ.mul hw.1).ennreal_ofReal) _

/-- The same actual optimal selector for Z is admissible for Y. No first
moment, finite distance, or witness for the desired inequality is assumed. -/
theorem primalTrim_le_add_couplingDistance (hY : Measurable Y) (hZ : Measurable Z)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hZ0 : ∀ ω, 0 ≤ Z ω) (hθ : 0 < θ ∧ θ < 1) :
    primalTrim θ μ Y ≤ primalTrim θ μ Z + couplingDistance μ Y Z := by
  obtain ⟨q, c, _, _, hs, hmin, _⟩ := exists_primal_minimizer hZ hZ0 hθ (μ := μ)
  rw [hmin]
  have hle : primalTrim θ μ Y ≤ selectorCost μ Y (thresholdWeight Z q c) :=
    sInf_le ⟨thresholdWeight Z q c, hs, rfl⟩
  exact hle.trans (selectorCost_le_add_couplingDistance hZ hs)

/-- The printed coupling inequality with the absolute difference interpreted
as an extended nonnegative expectation, valid also for infinite first moments. -/
theorem populationTrim_coupling_extended (hY : Measurable Y) (hZ : Measurable Z)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hZ0 : ∀ ω, 0 ≤ Z ω) (hθ : 0 < θ ∧ θ < 1) :
    ENNReal.ofReal |populationTrim θ μ Y - populationTrim θ μ Z| ≤ couplingDistance μ Y Z := by
  have h1 := primalTrim_le_add_couplingDistance hY hZ hY0 hZ0 hθ (μ := μ)
  have h2 := primalTrim_le_add_couplingDistance hZ hY hZ0 hY0 hθ (μ := μ)
  rw [← couplingDistance_symm (Y := Y) (Z := Z)] at h2
  rw [primalTrim_eq_populationTrim hY hY0 hθ, primalTrim_eq_populationTrim hZ hZ0 hθ] at h1 h2
  have hp := ThresholdSelectors.populationTrim_nonneg hY hY0 hθ (μ := μ)
  have hq := ThresholdSelectors.populationTrim_nonneg hZ hZ0 hθ (μ := μ)
  by_cases hd : couplingDistance μ Y Z = ∞
  · simp [hd]
  · have ht1 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hd⟩) h1
    have ht2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hd⟩) h2
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hd,
      ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq] at ht1 ht2
    have habs : |populationTrim θ μ Y - populationTrim θ μ Z| ≤ (couplingDistance μ Y Z).toReal :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    exact (ENNReal.ofReal_le_ofReal habs).trans_eq (ENNReal.ofReal_toReal hd)

/-- The ordinary real expectation version needs integrability only of the
difference. Both individual variables may have infinite expectation. -/
theorem populationTrim_coupling_finite_distance (hY : Measurable Y) (hZ : Measurable Z)
    (hY0 : ∀ ω, 0 ≤ Y ω) (hZ0 : ∀ ω, 0 ≤ Z ω) (hθ : 0 < θ ∧ θ < 1)
    (hD : Integrable (fun ω => |Y ω - Z ω|) μ) :
    |populationTrim θ μ Y - populationTrim θ μ Z| ≤ ∫ ω, |Y ω - Z ω| ∂μ := by
  have h := populationTrim_coupling_extended hY hZ hY0 hZ0 hθ (μ := μ)
  have he := ofReal_integral_eq_lintegral_ofReal hD (Eventually.of_forall fun ω => abs_nonneg (Y ω - Z ω))
  change ENNReal.ofReal |populationTrim θ μ Y - populationTrim θ μ Z| ≤
    ∫⁻ ω, ENNReal.ofReal |Y ω - Z ω| ∂μ at h
  rw [← he] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun ω => abs_nonneg (Y ω - Z ω))).mp h

#print axioms selectorCost_le_add_couplingDistance
#print axioms primalTrim_le_add_couplingDistance
#print axioms populationTrim_coupling_extended
#print axioms populationTrim_coupling_finite_distance
end NLA.IE21.GeneralCoupling
