module

public import NLA.IE21.PrintedRate.Definitions
public import NLA.IE21.FiniteSize
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
namespace NLA.IE21.PrintedRate

theorem actual_rate_formula (m n : ℕ) :
    rate m n = Real.sqrt ((n : ℝ) / m * Real.log ((m : ℝ) / n)) +
      (n : ℝ)^(-(1/2 : ℝ)) + (m : ℝ)⁻¹ := by
  rw [rate, Real.rpow_neg (Nat.cast_nonneg n), Real.sqrt_eq_rpow (n : ℝ)]

theorem actual_rate_constant_pos (θ : ℝ) (hθ : θ < 1) : 0 < rateConstant θ := by
  unfold rateConstant truncationScale
  positivity

theorem actual_finite_rate_error (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (ht : aspectParameter m n ≤ 1/2) :
    finiteRatioError θ m n (aspectParameter m n) (aspectParameter m n)
      (aspectParameter m n) ≤ rateConstant θ * rate m n := by
  have hL : 0 ≤ truncationScale θ := by
    unfold truncationScale
    exact div_nonneg (by norm_num) (sub_pos.mpr hθ.2).le
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ht0 : 0 ≤ aspectParameter m n := by unfold aspectParameter; positivity
  have hd : aspectParameter m n = 32 *
      Real.sqrt ((n : ℝ) / m * Real.log ((m : ℝ) / n)) := by
    unfold aspectParameter
    congr 2
    field_simp
  have hs : Real.sqrt (2 / (n : ℝ)) = Real.sqrt 2 * (Real.sqrt (n : ℝ))⁻¹ := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv]
  have htwo : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  let t := aspectParameter m n
  let B := (2 * truncationScale θ + 4) * t + truncationScale θ / m +
    Real.sqrt (2 / (n : ℝ))
  have hB : 0 ≤ B := by dsimp [B, t]; positivity
  have hden : 0 < 1-t := by dsimp [t]; linarith
  have hnum : trimmingError θ m t t t + Real.sqrt (2 / (n : ℝ)) + t ≤ B := by
    have hsq : t*t ≤ t/2 := by
      dsimp [t]
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht)]
    dsimp [trimmingError, B]
    nlinarith
  have he : finiteRatioError θ m n t t t ≤ 2*B := by
    unfold finiteRatioError
    apply (div_le_iff₀ hden).mpr
    have hbt : B * t ≤ B/2 := by
      dsimp [t]
      nlinarith [mul_nonneg hB (sub_nonneg.mpr ht)]
    nlinarith
  calc
    _ ≤ 2*B := he
    _ = (128 * truncationScale θ + 256) *
          Real.sqrt ((n : ℝ) / m * Real.log ((m : ℝ) / n)) +
        (2 * Real.sqrt 2) * (Real.sqrt (n : ℝ))⁻¹ +
        (2 * truncationScale θ) * (m : ℝ)⁻¹ := by
      dsimp [B, t]
      rw [hd, hs]
      ring
    _ ≤ rateConstant θ * Real.sqrt ((n : ℝ) / m * Real.log ((m : ℝ) / n)) +
        rateConstant θ * (Real.sqrt (n : ℝ))⁻¹ + rateConstant θ * (m : ℝ)⁻¹ := by
      gcongr <;> dsimp [rateConstant] <;> nlinarith
    _ = rateConstant θ * rate m n := by unfold rate; ring

theorem actual_rate_probability_limit (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    Tendsto (fun j => (matrixLaw (m j) (n j)).real
      {A | |deletionRatio θ A - gaussianTrim θ| >
        rateConstant θ * rate (m j) (n j)}) atTop (𝓝 0) := by
  obtain ⟨hadm, hfail, _⟩ := aspect_schedule θ hθ m n hm hn hnlim hQlim
  have hhalf := (aspectParameter_tendsto_zero m n hQlim).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  apply squeeze_zero' (Eventually.of_forall (fun j => measureReal_nonneg)) _ hfail
  filter_upwards [hadm, hhalf] with j hj hhalfj
  let d := aspectParameter (m j) (n j)
  let : IsProbabilityMeasure (matrixLaw (m j) (n j)) :=
    (product_row_semantics (m j) (n j) (hn j)).1
  have he := actual_finite_rate_error θ hθ (m j) (n j) (hm j) (hn j) hhalfj.le
  have hs : {A : Mat (m j) (n j) | |deletionRatio θ A - gaussianTrim θ| >
      rateConstant θ * rate (m j) (n j)} ⊆
      {A | |deletionRatio θ A - gaussianTrim θ| >
        finiteRatioError θ (m j) (n j) d d d} := by
    intro A hA
    exact lt_of_le_of_lt he hA
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    (product_ratio_tail_bound θ hθ (m j) (n j) (hm j) hj.1 d d d
      ⟨hj.2.1, hj.2.2.1⟩ ⟨hj.2.1, hj.2.2.2⟩ ⟨hj.2.1, hj.2.2.1⟩)

#print axioms actual_rate_formula
#print axioms actual_rate_constant_pos
#print axioms actual_finite_rate_error
#print axioms actual_rate_probability_limit
end NLA.IE21.PrintedRate
