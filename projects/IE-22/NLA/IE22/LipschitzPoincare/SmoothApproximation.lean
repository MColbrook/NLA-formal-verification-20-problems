module

public import NLA.IE22.LipschitzPoincare.Bounded
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
namespace NLA.IE22.LipschitzPoincare
open NLA.IE21

def atanTruncate (n : ℕ) (z : ℝ) : ℝ :=
  ((n : ℝ) + 1) * Real.arctan (z / ((n : ℝ) + 1))

theorem atanTruncate_hasDerivAt (n : ℕ) (z : ℝ) :
    HasDerivAt (atanTruncate n) (1 / (1 + (z / ((n : ℝ) + 1)) ^ 2)) z := by
  have hR : (n : ℝ) + 1 ≠ 0 := by positivity
  have h := ((Real.hasDerivAt_arctan (z / ((n : ℝ) + 1))).comp z
    ((hasDerivAt_id z).div_const ((n : ℝ) + 1))).const_mul ((n : ℝ) + 1)
  convert h using 1 <;> first | rfl | field_simp

theorem atanTruncate_coefficient (n : ℕ) (z : ℝ) :
    0 ≤ 1 / (1 + (z / ((n : ℝ) + 1)) ^ 2) ∧
      1 / (1 + (z / ((n : ℝ) + 1)) ^ 2) ≤ 1 := by
  constructor
  · positivity
  · exact (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg (z / ((n : ℝ)+1))])

theorem atanTruncate_lipschitz (n : ℕ) : LipschitzWith 1 (atanTruncate n) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun z => (atanTruncate_hasDerivAt n z).differentiableAt)
  intro z
  rw [(atanTruncate_hasDerivAt n z).deriv]
  exact_mod_cast (show ‖(1 / (1 + (z / ((n : ℝ) + 1)) ^ 2) : ℝ)‖ ≤ 1 by
    rw [Real.norm_eq_abs, abs_of_nonneg (atanTruncate_coefficient n z).1]
    exact (atanTruncate_coefficient n z).2)

theorem atanTruncate_abs_le (n : ℕ) (z : ℝ) : |atanTruncate n z| ≤ |z| := by
  have h := (atanTruncate_lipschitz n).dist_le_mul z 0
  simpa [Real.dist_eq, atanTruncate, Real.arctan_zero] using h

theorem atanTruncate_bounded (n : ℕ) :
    ∀ z, |atanTruncate n z| ≤ ((n : ℝ) + 1) * (Real.pi / 2) := by
  intro z
  rw [atanTruncate, abs_mul, abs_of_pos (show 0 < (n : ℝ) + 1 by positivity)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le,
    (Real.arctan_lt_pi_div_two _).le⟩

theorem atanTruncate_tendsto (z : ℝ) : Tendsto (fun n => atanTruncate n z) atTop (𝓝 z) := by
  have hd : HasDerivAt (fun t : ℝ => Real.arctan (t * z)) z 0 := by
    convert (Real.hasDerivAt_arctan (0 * z)).comp 0 ((hasDerivAt_id (0 : ℝ)).mul_const z) using 1 <;>
      first | rfl | simp
  have hu : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  have h := hd.tendsto_slope_zero_right.comp hu
  simpa [atanTruncate, smul_eq_mul, div_eq_mul_inv, mul_comm, Function.comp_def] using h

#print axioms atanTruncate_tendsto
end NLA.IE22.LipschitzPoincare
