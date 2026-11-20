module

public import NLA.MD06.CycleProfile.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CycleProfile
open scoped BigOperators
open Set

theorem actual_arcsin_lower {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ≤ Real.arcsin x := by
  have h := Real.sin_le (Real.arcsin_nonneg.mpr h0)
  rwa [Real.sin_arcsin (by linarith) h1] at h

theorem actual_arcsin_chord {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.arcsin x ≤ Real.pi / 2 * x := by
  apply (Real.arcsin_le_iff_le_sin ⟨by linarith, h1⟩ ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩).mpr
  exact Real.le_sin_mul h0 h1

theorem actual_arcsin_half : Real.arcsin (1/2 : ℝ) = Real.pi / 6 := by
  rw [← Real.sin_pi_div_six]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

theorem actual_geometric_tail_le (R : ℕ) : ∑ j ∈ Finset.Ico 1 R, 1 / (2 : ℝ)^j ≤ 1 := by
  by_cases h : 1 ≤ R
  · have he : (∑ j ∈ Finset.Ico 1 R, 1 / (2 : ℝ)^j) =
        ((1/2 : ℝ) - (1/2 : ℝ)^R) / (1 - (1/2 : ℝ)) := by
      simp only [one_div, ← inv_pow]
      simpa using geom_sum_Ico' (x := (1/2 : ℝ)) (by norm_num) h
    rw [he]
    have hp : 0 ≤ (1/2 : ℝ)^R := by positivity
    norm_num
    linarith
  · have : R = 0 := by omega
    simp [this]

theorem actual_delta_nonneg {t : ℝ} (ht : 0 ≤ t) (j : ℕ) : 0 ≤ Delta t j :=
  Real.arcsin_nonneg.mpr (by positivity)

theorem actual_balance_zero (R : ℕ) : Balance R 0 = 0 := by
  simp [Balance, Delta]

theorem actual_balance_continuous (R : ℕ) : Continuous (Balance R) := by
  unfold Balance Delta
  fun_prop

theorem actual_balance_strictMono (R : ℕ) : StrictMonoOn (Balance R) (Icc 0 1) := by
  intro x hx y hy hxy
  have hfirst : Real.arcsin x < Real.arcsin y := Real.arcsin_lt_arcsin (by linarith [hx.1]) hxy hy.2
  have hsum : (∑ j ∈ Finset.Ico 1 R, Delta x j) ≤ ∑ j ∈ Finset.Ico 1 R, Delta y j := by
    apply Finset.sum_le_sum
    intro j hj
    exact Real.arcsin_le_arcsin (div_le_div_of_nonneg_right hxy.le (by positivity))
  unfold Balance
  linarith

theorem actual_balance_radius_monotone {R S : ℕ} (hRS : R ≤ S) {t : ℝ} (ht : 0 ≤ t) :
    Balance R t ≤ Balance S t := by
  have hsum : (∑ j ∈ Finset.Ico 1 R, Delta t j) ≤ ∑ j ∈ Finset.Ico 1 S, Delta t j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hRS)
      (by intro j hj hjR; exact actual_delta_nonneg ht j)
  unfold Balance
  linarith

theorem actual_balance_one_gt {R : ℕ} (hR : 4 ≤ R) : 2 * Real.pi < Balance R 1 := by
  have h4 : 2 * Real.pi < Balance 4 1 := by
    norm_num [Balance, Delta, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ,
      actual_arcsin_half, Real.arcsin_one]
    have hq := actual_arcsin_lower (x := (1/4 : ℝ)) (by norm_num) (by norm_num)
    have he := actual_arcsin_lower (x := (1/8 : ℝ)) (by norm_num) (by norm_num)
    linarith [Real.pi_lt_four]
  exact h4.trans_le (actual_balance_radius_monotone hR (by norm_num))

theorem actual_balance_half_lt (R : ℕ) : Balance R (1/2) < 2 * Real.pi := by
  have hterm : ∀ j ∈ Finset.Ico 1 R, Delta (1/2) j ≤ Real.pi / 4 * (1 / (2 : ℝ)^j) := by
    intro j hj
    have hj0 : 0 ≤ (1/2 : ℝ) / 2^j := by positivity
    have hj1 : (1/2 : ℝ) / 2^j ≤ 1 := by
      have hp : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^j)).mpr
      linarith
    have hh := actual_arcsin_chord hj0 hj1
    unfold Delta
    convert hh using 1
    ring
  have hs := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum] at hs
  have ht := actual_geometric_tail_le R
  have hmul : Real.pi / 4 * (∑ j ∈ Finset.Ico 1 R, 1 / (2 : ℝ)^j) ≤ Real.pi / 4 := by
    nlinarith [Real.pi_pos]
  unfold Balance
  rw [actual_arcsin_half]
  linarith [Real.pi_pos]
end Reference.MD06CycleProfile
