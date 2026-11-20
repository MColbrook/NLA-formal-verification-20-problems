module

public import NLA.MD06.SpectralTraceBound.GapRootBounds
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06CenteredMarkov
open Reference.RootMD06SpectralTrace Filter
open scoped Topology

theorem actual_gap_ratio_polynomial_power_tendsto_zero (d : ℕ) :
    Tendsto (fun k : ℕ => (k : ℝ) ^ d * (8 / GapRoot ^ 4) ^ k) atTop (𝓝 0) := by
  apply Summable.tendsto_atTop_zero
  apply summable_pow_mul_geometric_of_norm_lt_one
  rw [Real.norm_eq_abs, abs_of_pos actual_gap_root_geometric_ratio_bounds.1]
  exact actual_gap_root_geometric_ratio_bounds.2

theorem actual_gap_ratio_shifted_polynomial_power_tendsto_zero (d : ℕ) :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1) ^ d * (8 / GapRoot ^ 4) ^ k)
      atTop (𝓝 0) := by
  let r : ℝ := 8 / GapRoot ^ 4
  have hr : r ≠ 0 := ne_of_gt actual_gap_root_geometric_ratio_bounds.1
  have h := (actual_gap_ratio_polynomial_power_tendsto_zero d).comp
    (tendsto_add_atTop_nat 1)
  have hd := h.div_const r
  simp only [zero_div] at hd
  convert hd using 1
  funext k
  change ((k : ℝ) + 1) ^ d * r ^ k = ((k + 1 : ℕ) : ℝ) ^ d * r ^ (k + 1) / r
  rw [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp [hr]

theorem actual_dyadic_center_error_bound (k : ℕ) (n : ℝ)
    (hu : n ≤ (2 : ℝ) ^ (k + 1)) :
    n * (2 : ℝ) ^ (2 * k) / GapRoot ^ (4 * k) ≤
      2 * (8 / GapRoot ^ 4) ^ k := by
  have hR : 0 < GapRoot := by linarith [actual_gap_root_rational_bounds.1]
  have hp2 : (2 : ℝ) ^ (2 * k) = (4 : ℝ) ^ k := by rw [pow_mul]; norm_num
  have hpR : GapRoot ^ (4 * k) = (GapRoot ^ 4) ^ k := pow_mul _ _ _
  have hp8 : (8 : ℝ) ^ k = (2 : ℝ) ^ k * (4 : ℝ) ^ k := by
    rw [show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]
  calc
    n * (2 : ℝ) ^ (2 * k) / GapRoot ^ (4 * k) ≤
        (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k) / GapRoot ^ (4 * k) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu (by positivity))
        (pow_nonneg hR.le _)
    _ = _ := by rw [hp2, hpR, pow_succ, div_pow, hp8]; ring

theorem actual_dyadic_trace_error_bound (k : ℕ) (n : ℝ)
    (hl : (2 : ℝ) ^ k ≤ n) :
    ((2 : ℝ) ^ (4 * k) / n) / GapRoot ^ (4 * k) ≤
      (8 / GapRoot ^ 4) ^ k := by
  have hR : 0 < GapRoot := by linarith [actual_gap_root_rational_bounds.1]
  have hn : 0 < n := lt_of_lt_of_le (by positivity) hl
  have hprod : (2 : ℝ) ^ (4 * k) ≤ (8 : ℝ) ^ k * n := by
    calc
      (2 : ℝ) ^ (4 * k) = (8 : ℝ) ^ k * (2 : ℝ) ^ k := by
        rw [pow_mul, ← mul_pow]
        norm_num
      _ ≤ (8 : ℝ) ^ k * n := mul_le_mul_of_nonneg_left hl (by positivity)
  have hdiv : (2 : ℝ) ^ (4 * k) / n ≤ (8 : ℝ) ^ k := (div_le_iff₀ hn).2 hprod
  calc
    _ ≤ (8 : ℝ) ^ k / GapRoot ^ (4 * k) := div_le_div_of_nonneg_right hdiv (pow_nonneg hR.le _)
    _ = _ := by rw [pow_mul, div_pow]

theorem actual_dyadic_polynomial_trace_error_bound (k d : ℕ) (n a b : ℝ)
    (hl : (2 : ℝ) ^ k ≤ n) (hu : n ≤ (2 : ℝ) ^ (k + 1))
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a * ((k : ℝ) + 1) ^ d * ((2 : ℝ) ^ (4 * k) / n) +
      b * n * (2 : ℝ) ^ (2 * k)) / GapRoot ^ (4 * k) ≤
      (a * ((k : ℝ) + 1) ^ d + 2 * b) * (8 / GapRoot ^ 4) ^ k := by
  have h1 := actual_dyadic_trace_error_bound k n hl
  have h2 := actual_dyadic_center_error_bound k n hu
  have hp : 0 ≤ a * ((k : ℝ) + 1) ^ d := by positivity
  have he : (a * ((k : ℝ) + 1) ^ d * ((2 : ℝ) ^ (4 * k) / n) +
      b * n * (2 : ℝ) ^ (2 * k)) / GapRoot ^ (4 * k) =
      a * ((k : ℝ) + 1) ^ d * (((2 : ℝ) ^ (4 * k) / n) / GapRoot ^ (4 * k)) +
      b * (n * (2 : ℝ) ^ (2 * k) / GapRoot ^ (4 * k)) := by ring
  rw [he]
  calc
    _ ≤ a * ((k : ℝ) + 1) ^ d * (8 / GapRoot ^ 4) ^ k +
        b * (2 * (8 / GapRoot ^ 4) ^ k) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 hp) (mul_le_mul_of_nonneg_left h2 hb)
    _ = _ := by ring

theorem actual_dyadic_polynomial_trace_envelope_tendsto_zero (d : ℕ) (a b : ℝ) :
    Tendsto (fun k : ℕ => (a * ((k : ℝ) + 1) ^ d + 2 * b) *
      (8 / GapRoot ^ 4) ^ k) atTop (𝓝 0) := by
  have h1 := (actual_gap_ratio_shifted_polynomial_power_tendsto_zero d).const_mul a
  have h2 := (actual_gap_ratio_polynomial_power_tendsto_zero 0).const_mul (2 * b)
  have h := h1.add h2
  simp only [mul_zero, add_zero, pow_zero, one_mul] at h
  convert h using 1
  funext k
  ring

#print axioms actual_gap_ratio_polynomial_power_tendsto_zero
#print axioms actual_gap_ratio_shifted_polynomial_power_tendsto_zero
#print axioms actual_dyadic_center_error_bound
#print axioms actual_dyadic_trace_error_bound
#print axioms actual_dyadic_polynomial_trace_error_bound
#print axioms actual_dyadic_polynomial_trace_envelope_tendsto_zero
end Reference.RootMD06CenteredMarkov
