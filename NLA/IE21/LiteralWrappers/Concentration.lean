module

public import NLA.IE21.LiteralWrappers.QuantileBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace NLA.IE21.LiteralWrappers
open QuantileIntegral ContinuousTruncation

theorem mean_deviation_scale {m : ℕ} (hm : 1 ≤ m) (S a : ℝ) :
    |S - m*a| = (m : ℝ) * |S/m-a| := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  calc
    |S - m*a| = |(m : ℝ)*(S/m-a)| := by congr 1; field_simp
    _ = (m : ℝ)*|S/m-a| := by rw [abs_mul, abs_of_pos hm0]

theorem fixed_quantile_two_tails {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {m : ℕ} (hm : 1 ≤ m) (R : Fin m → Ω → Ξ)
    (hR : ∀ i, Measurable (R i)) (hind : iIndepFun R ν)
    (hlaw : ∀ i, ν.map (R i) = μ) (Y : Ξ → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y μ) (hY0 : ∀ z, 0 ≤ Y z)
    (hmean : ∫ z, Y z ∂μ = 1) [NullSingletonClass (μ.map Y)]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (ε : ℝ) (hε : 0 ≤ ε) :
    let b := lowerQuantile (μ.map Y) θ
    ν.real {ω |
      ε < |(∑ i, {z | Y z ≤ b}.indicator (fun _ => (1 : ℝ)) (R i ω)) / m - θ| ∨
      b*ε < |(∑ i, {z | Y z ≤ b}.indicator Y (R i ω)) / m - populationTrim θ μ Y|} ≤
      4 * Real.exp (-2 * (m : ℝ) * ε^2) := by
  let b := lowerQuantile (μ.map Y) θ
  let W : Ξ → ℝ := {z | Y z ≤ b}.indicator (fun _ => 1)
  let Z : Ξ → ℝ := {z | Y z ≤ b}.indicator Y
  have hb := actual_quantile_bounds μ Y hYm hY hY0 hmean θ hθ
  have hs : MeasurableSet {z | Y z ≤ b} := measurableSet_le hYm measurable_const
  have hWm : Measurable W := measurable_const.indicator hs
  have hZm : Measurable Z := hYm.indicator hs
  have hWb (z : Ξ) : W z ∈ Icc 0 1 := by dsimp [W, Set.indicator]; split_ifs <;> norm_num
  have hZb (z : Ξ) : Z z ∈ Icc 0 b := by
    dsimp [Z, Set.indicator]
    split_ifs with hz
    · exact ⟨hY0 z, hz⟩
    · exact ⟨le_rfl, hb.1.le⟩
  have hWi : ∫ z, W z ∂μ = θ := by
    rw [show W = {z | Y z ≤ b}.indicator (fun _ => (1 : ℝ)) from rfl,
      integral_indicator hs, setIntegral_const, hb.2.2.2.1]
    simp
  have hZi : ∫ z, Z z ∂μ = populationTrim θ μ Y := hb.2.2.2.2.symm
  have transfer (F : Ξ → ℝ) (hF : Measurable F) (i : Fin m) :
      (∫ ω, F (R i ω) ∂ν) = ∫ z, F z ∂μ := by
    rw [← integral_map (hR i).aemeasurable hF.aestronglyMeasurable, hlaw i]
  have hw := bounded_sum_abs_tail ν hm (fun i ω => W (R i ω))
    (fun i => hWm.comp (hR i)) (hind.comp (fun _ => W) (fun _ => hWm))
    1 zero_lt_one (fun i => Eventually.of_forall fun ω => hWb (R i ω)) θ
    (fun i => (transfer W hWm i).trans hWi) ε hε
  have hz := bounded_sum_abs_tail ν hm (fun i ω => Z (R i ω))
    (fun i => hZm.comp (hR i)) (hind.comp (fun _ => Z) (fun _ => hZm))
    b hb.1 (fun i => Eventually.of_forall fun ω => hZb (R i ω)) (populationTrim θ μ Y)
    (fun i => (transfer Z hZm i).trans hZi) ε hε
  let EW := {ω | (m : ℝ)*ε < |(∑ i, W (R i ω))-m*θ|}
  let EZ := {ω | (m : ℝ)*b*ε < |(∑ i, Z (R i ω))-m*populationTrim θ μ Y|}
  have hsub : {ω | ε < |(∑ i, W (R i ω))/m-θ| ∨
      b*ε < |(∑ i, Z (R i ω))/m-populationTrim θ μ Y|} ⊆ EW ∪ EZ := by
    intro ω hω
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    rcases hω with hw | hz
    · left
      change (m : ℝ)*ε < |(∑ i, W (R i ω))-m*θ|
      rw [mean_deviation_scale hm]
      exact mul_lt_mul_of_pos_left hw hm0
    · right
      change (m : ℝ)*b*ε < |(∑ i, Z (R i ω))-m*populationTrim θ μ Y|
      rw [mean_deviation_scale hm, mul_assoc]
      exact mul_lt_mul_of_pos_left hz hm0
  have hu := ((measureReal_mono (μ := ν) hsub).trans (measureReal_union_le EW EZ))
  simp only [mul_one] at hw
  exact hu.trans (by dsimp [EW, EZ]; linarith)

theorem large_threshold_count_tail {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {m : ℕ} (hm : 1 ≤ m) (R : Fin m → Ω → Ξ)
    (hR : ∀ i, Measurable (R i)) (hind : iIndepFun R ν)
    (hlaw : ∀ i, ν.map (R i) = μ) (Y : Ξ → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y μ) (hY0 : ∀ z, 0 ≤ Y z)
    (hmean : ∫ z, Y z ∂μ = 1) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ν.real {ω | (Finset.univ.filter (fun i => Y (R i ω) ≤ truncationScale θ)).card < retainedRows θ m} ≤
      Real.exp (-(m : ℝ)*(1-θ)^2/2) := by
  classical
  let L := truncationScale θ
  let C : Ξ → ℝ := {z | Y z ≤ L}.indicator (fun _ => 1)
  have hCm : Measurable C := measurable_const.indicator (measurableSet_le hYm measurable_const)
  have hCb (z : Ξ) : C z ∈ Icc 0 1 := by dsimp [C, Set.indicator]; split_ifs <;> norm_num
  let q : ℝ := μ.real {z | Y z ≤ L}
  have hq : (1+θ)/2 ≤ q := mean_one_large_threshold_mass μ Y hYm hY hY0 hmean θ hθ
  have hc := bounded_sum_lower_tail ν hm (fun i ω => C (R i ω))
    (fun i => hCm.comp (hR i)) (hind.comp (fun _ => C) (fun _ => hCm))
    1 zero_lt_one (fun i => Eventually.of_forall fun ω => hCb (R i ω)) q
    (fun i => by
      rw [← integral_map (hR i).aemeasurable hCm.aestronglyMeasurable, hlaw i]
      simp [C, q, integral_indicator, measurableSet_le hYm measurable_const])
    ((1-θ)/2) (by linarith [hθ.2])
  have hsub : {ω | (Finset.univ.filter (fun i => Y (R i ω) ≤ L)).card < retainedRows θ m} ⊆
      {ω | (m : ℝ)*1*((1-θ)/2) < m*q-∑ i, C (R i ω)} := by
    intro ω hω
    have hsum : (∑ i, C (R i ω)) =
        ((Finset.univ.filter (fun i => Y (R i ω) ≤ L)).card : ℝ) := by simp [C, Set.indicator]
    change (m : ℝ)*1*((1-θ)/2) < m*q-∑ i, C (R i ω)
    rw [hsum]
    have hk := (retainedRows_bounds θ hθ m).2.1
    have hh : ((Finset.univ.filter (fun i => Y (R i ω) ≤ L)).card : ℝ) < retainedRows θ m := by exact_mod_cast hω
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    nlinarith
  have he : -2*(m : ℝ)*((1-θ)/2)^2 = -(m : ℝ)*(1-θ)^2/2 := by ring
  rw [he] at hc
  exact (measureReal_mono hsub).trans hc

#print axioms fixed_quantile_two_tails
#print axioms large_threshold_count_tail
end NLA.IE21.LiteralWrappers
