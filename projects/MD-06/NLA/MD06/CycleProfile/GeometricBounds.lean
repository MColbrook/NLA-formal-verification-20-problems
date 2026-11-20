module

public import NLA.MD06.CycleProfile.Roots
public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CycleProfile
open scoped BigOperators
open Set

theorem actual_arcsin_scale_le {t a : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.arcsin (a * t) ≤ a * Real.arcsin t := by
  have hu0 : 0 ≤ Real.arcsin t := Real.arcsin_nonneg.mpr ht0
  have hu1 : Real.arcsin t ≤ Real.pi := by
    linarith [Real.arcsin_le_pi_div_two t, Real.pi_pos]
  have hs : (1-a) * Real.sin 0 + a * Real.sin (Real.arcsin t) ≤
      Real.sin ((1-a) * 0 + a * Real.arcsin t) :=
    strictConcaveOn_sin_Icc.concaveOn.2 ⟨le_rfl, Real.pi_pos.le⟩ ⟨hu0, hu1⟩
      (sub_nonneg.mpr ha1) ha0 (by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add,
    Real.sin_arcsin (by linarith : -1 ≤ t) ht1] at hs
  have hat : a*t ≤ 1 := calc
    a*t ≤ 1*t := mul_le_mul_of_nonneg_right ha1 ht0
    _ ≤ 1 := by simpa using ht1
  have hau : a*Real.arcsin t ≤ Real.pi/2 := calc
    a*Real.arcsin t ≤ 1*Real.arcsin t := mul_le_mul_of_nonneg_right ha1 hu0
    _ ≤ Real.pi/2 := by simpa using Real.arcsin_le_pi_div_two t
  apply (Real.arcsin_le_iff_le_sin
    (show a*t ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [mul_nonneg ha0 ht0], hat⟩)
    (show a * Real.arcsin t ∈ Icc (-(Real.pi/2)) (Real.pi/2) from
      ⟨by linarith [mul_nonneg ha0 hu0, Real.pi_pos], hau⟩)).mpr
  exact hs

theorem actual_delta_geometric {t : ℝ} (ht : t ∈ Icc 0 1) (j : ℕ) :
    Delta t j ≤ Real.arcsin t * (1 / (2 : ℝ)^j) := by
  have hp : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have ha : 1 / (2 : ℝ)^j ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^j)).mpr
    simpa using hp
  simpa [Delta, div_eq_mul_inv, mul_comm] using
    actual_arcsin_scale_le ht.1 ht.2 (by positivity : 0 ≤ 1 / (2 : ℝ)^j) ha

theorem actual_geometric_tail_lt (R : ℕ) : ∑ j ∈ Finset.Ico 1 R, 1 / (2 : ℝ)^j < 1 := by
  by_cases h : 1 ≤ R
  · have he : (∑ j ∈ Finset.Ico 1 R, 1 / (2 : ℝ)^j) =
        ((1/2 : ℝ) - (1/2 : ℝ)^R) / (1 - (1/2 : ℝ)) := by
      simp only [one_div, ← inv_pow]
      simpa using geom_sum_Ico' (x := (1/2 : ℝ)) (by norm_num) h
    rw [he]
    have hp : 0 < (1/2 : ℝ)^R := by positivity
    norm_num
    linarith
  · have : R = 0 := by omega
    simp [this]

theorem actual_balance_lt_five {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (R : ℕ) :
    Balance R t < 5 * Real.arcsin t := by
  have hs := Finset.sum_le_sum (fun j (_hj : j ∈ Finset.Ico 1 R) =>
    actual_delta_geometric ⟨ht0.le, ht1⟩ j)
  rw [← Finset.mul_sum] at hs
  have hp : 0 < Real.arcsin t := Real.arcsin_pos.mpr ht0
  have hm := mul_lt_mul_of_pos_left (actual_geometric_tail_lt R) hp
  unfold Balance
  linarith

theorem actual_root_delta_geometric {R : ℕ} (hR : 4 ≤ R) (j : ℕ) :
    Delta (Root R) j ≤ Delta (Root R) 0 * (1 / (2 : ℝ)^j) := by
  simpa [Delta] using actual_delta_geometric (actual_root_spec hR).1 j

theorem actual_root_balance_lt_five {R : ℕ} (hR : 4 ≤ R) :
    2 * Real.pi < 5 * Delta (Root R) 0 := by
  have hi := actual_root_interval hR
  have hpos : 0 < Root R := lt_trans (by norm_num : (0 : ℝ) < 1/2) hi.1
  have hb := actual_balance_lt_five hpos hi.2.le R
  rw [(actual_root_spec hR).2] at hb
  simpa [Delta] using hb

theorem actual_root_delta_zero_gt {R : ℕ} (hR : 4 ≤ R) :
    2 * Real.pi / 5 < Delta (Root R) 0 := by
  linarith [actual_root_balance_lt_five hR]

end Reference.MD06CycleProfile
