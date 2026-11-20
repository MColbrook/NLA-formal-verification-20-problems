module

public import NLA.MD06.CycleProfile.NumericMargin

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CycleProfile
open scoped BigOperators
open Set

theorem actual_delta_argument_bounds {t : ℝ} (ht : t ∈ Icc 0 1) (j : ℕ) :
    t / (2 : ℝ)^j ∈ Icc 0 1 := by
  have hp : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  refine ⟨div_nonneg ht.1 (by positivity), ?_⟩
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^j)).mpr
  linarith [ht.2]

theorem actual_delta_sine {t : ℝ} (ht : t ∈ Icc 0 1) (j : ℕ) :
    Real.sin (Delta t j) = t / (2 : ℝ)^j := by
  have h := actual_delta_argument_bounds ht j
  exact Real.sin_arcsin (by linarith [h.1]) h.2

theorem actual_height_step {R j : ℕ} (hj : j < R) (t : ℝ) :
    Height R t j - Height R t (j+1) = Delta t j := by
  have h := Finset.sum_eq_sum_Ico_succ_bot hj (Delta t)
  unfold Height
  linarith

theorem actual_height_terminal (R : ℕ) (t : ℝ) : Height R t R = 0 := by simp [Height]

theorem actual_height_balance {R : ℕ} (hR : 1 ≤ R) (t : ℝ) :
    2 * Height R t 0 + Delta t 0 = Balance R t := by
  have h := Finset.sum_eq_sum_Ico_succ_bot (by omega : 0 < R) (Delta t)
  unfold Height Balance
  have hd : Delta t 0 = Real.arcsin t := by simp [Delta]
  rw [hd] at h ⊢
  linarith

theorem actual_root_height_balance {R : ℕ} (hR : 4 ≤ R) :
    2 * Height R (Root R) 0 + Delta (Root R) 0 = 2 * Real.pi := by
  rw [actual_height_balance (by omega : 1 ≤ R)]
  exact (actual_root_spec hR).2

theorem actual_opposite_root_sine {R : ℕ} (hR : 4 ≤ R) :
    Real.sin (2 * Height R (Root R) 0) = -Root R := by
  have h := actual_root_height_balance hR
  have he : 2 * Height R (Root R) 0 = 2 * Real.pi - Delta (Root R) 0 := by linarith
  rw [he,Real.sin_sub]
  simp [Real.sin_two_pi,Real.cos_two_pi,actual_delta_sine (actual_root_spec hR).1]

theorem actual_opposite_root_cosine {R : ℕ} (hR : 4 ≤ R) :
    Real.cos (2 * Height R (Root R) 0) = Real.sqrt (1-(Root R)^2) := by
  have h := actual_root_height_balance hR
  have he : 2 * Height R (Root R) 0 = 2 * Real.pi - Delta (Root R) 0 := by linarith
  rw [he,Real.cos_sub]
  simp [Real.sin_two_pi,Real.cos_two_pi,Delta,Real.cos_arcsin]

theorem actual_binary_tree_force_cancellation {t : ℝ} (ht : t ∈ Icc 0 1) (j : ℕ) :
    -Real.sin (Delta t j) + 2 * Real.sin (Delta t (j+1)) = 0 := by
  rw [actual_delta_sine ht,actual_delta_sine ht]
  rw [pow_succ]
  field_simp
  ring

theorem actual_root_force_cancellation {R : ℕ} (hR : 4 ≤ R) :
    Real.sin (2 * Height R (Root R) 0) + Real.sin (Delta (Root R) 0) = 0 := by
  rw [actual_opposite_root_sine hR,actual_delta_sine (actual_root_spec hR).1]
  simp

theorem actual_delta_cosine_uniform {R : ℕ} (hR : 4 ≤ R) (j : ℕ) :
    Real.sqrt (1-(Root 4)^2) ≤ Real.cos (Delta (Root R) j) := by
  rw [Delta,Real.cos_arcsin]
  apply (actual_root_uniform_cosine hR).trans
  apply Real.sqrt_le_sqrt
  have hr := actual_root_spec hR
  have ha := actual_delta_argument_bounds hr.1 j
  have hp : (1 : ℝ) ≤ 2^j := one_le_pow₀ (by norm_num)
  have hd : Root R / (2 : ℝ)^j ≤ Root R := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2^j)).mpr
    nlinarith [hr.1.1]
  nlinarith [ha.1,hr.1.1]

theorem actual_profile_tree_cosine_gt_sixteenth {R : ℕ} (hR : 4 ≤ R) (j : ℕ) :
    (1/16 : ℝ) < Real.cos (Delta (Root R) j) :=
  actual_uniform_cosine_gt_sixteenth.trans_le (actual_delta_cosine_uniform hR j)

theorem actual_profile_cycle_cosine_gt_sixteenth {R : ℕ} (hR : 4 ≤ R) :
    (1/16 : ℝ) < Real.cos (2 * Height R (Root R) 0) := by
  rw [actual_opposite_root_cosine hR]
  exact actual_uniform_cosine_gt_sixteenth.trans_le (actual_root_uniform_cosine hR)
end Reference.MD06CycleProfile
