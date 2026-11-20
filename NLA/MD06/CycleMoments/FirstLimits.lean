module

public import NLA.MD06.CyclePairPatterns.FirstMoment
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CycleMoments
open Reference.MD06CyclePairPatterns Reference.MD06PairingCounts Reference.MD06FiniteProbability
open Filter Topology
open scoped BigOperators

theorem actual_normalized_nat_affine_limit (a b : ℕ) (ha : 1 ≤ a) :
    Tendsto (fun n : ℕ => ((a*n-b : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 (a : ℝ)) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ => (a : ℝ) - (b : ℝ)*(n : ℝ)⁻¹)
      atTop (𝓝 ((a : ℝ) - (b : ℝ)*0)) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (a : ℝ)) atTop (𝓝 (a : ℝ))).sub
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (b : ℝ)) atTop (𝓝 (b : ℝ))).mul hi)
  have hh : Tendsto (fun n : ℕ => (a : ℝ) - (b : ℝ)*(n : ℝ)⁻¹)
      atTop (𝓝 (a : ℝ)) := by simpa using h
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (max b 1)] with n hn
  have hnb : b ≤ n := le_trans (le_max_left _ _) hn
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hba : b ≤ a*n := le_trans hnb (by nlinarith)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  rw [Nat.cast_sub hba,Nat.cast_mul]
  field_simp

theorem actual_normalized_desc_factorial_limit (ell : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial ell : ℝ)/(n : ℝ)^ell)
      atTop (𝓝 1) := by
  induction ell with
  | zero => simp
  | succ ell ih =>
    have hl := actual_normalized_nat_affine_limit 1 ell (by omega)
    have hprod := hl.mul ih
    simp only [Nat.cast_one,one_mul] at hprod
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    simp only [Nat.descFactorial_succ,Nat.cast_mul,pow_succ]
    field_simp

theorem actual_normalized_pairing_denominator_limit (ell : ℕ) :
    Tendsto (fun n : ℕ => (PairingDenominator n ell : ℝ)/(n : ℝ)^ell)
      atTop (𝓝 ((3 : ℝ)^ell)) := by
  induction ell with
  | zero => simp [PairingDenominator]
  | succ ell ih =>
    have hl := actual_normalized_nat_affine_limit 3 (2*ell+1) (by omega)
    have hprod := ih.mul hl
    simp only [Nat.cast_ofNat,← pow_succ] at hprod
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hs : 3*n-2*ell-1 = 3*n-(2*ell+1) := by omega
    simp only [PairingDenominator,Finset.prod_range_succ,Nat.cast_mul,hs,pow_succ]
    field_simp

theorem actual_oriented_formula_limit (ell : ℕ) :
    Tendsto (fun n : ℕ => (n.descFactorial ell : ℝ)*(6 : ℝ)^ell /
      (PairingDenominator n ell : ℝ)) atTop (𝓝 ((2 : ℝ)^ell)) := by
  have ht := (actual_normalized_desc_factorial_limit ell).div
    (actual_normalized_pairing_denominator_limit ell) (by positivity)
  have hm := ht.mul_const ((6 : ℝ)^ell)
  have hc : (1 / (3 : ℝ)^ell) * 6^ell = 2^ell := by
    rw [one_div,inv_mul_eq_div,← div_pow]
    norm_num
  rw [hc] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [Pi.div_apply]
  field_simp [hn0]

theorem actual_mean_oriented_cycles_limit (ell : ℕ) :
    Tendsto (fun k : ℕ => MeanOrientedCycles k ell) atTop (𝓝 ((2 : ℝ)^ell)) := by
  have hs : Tendsto Size atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    simp only [Size]
    omega
  exact ((actual_oriented_formula_limit ell).comp hs).congr
    (fun k => (actual_mean_oriented_cycles_formula k ell).symm)

#print axioms actual_normalized_nat_affine_limit
#print axioms actual_normalized_desc_factorial_limit
#print axioms actual_normalized_pairing_denominator_limit
#print axioms actual_oriented_formula_limit
#print axioms actual_mean_oriented_cycles_limit
end Reference.MD06CycleMoments