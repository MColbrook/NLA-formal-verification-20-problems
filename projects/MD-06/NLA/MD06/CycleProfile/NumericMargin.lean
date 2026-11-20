module

public import NLA.MD06.CycleProfile.Roots
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CycleProfile
open Set

theorem actual_arcsin_derivative_lower {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    1 + x^2/2 ≤ 1 / Real.sqrt (1-x^2) := by
  have hx : 0 < 1-x^2 := by nlinarith
  have hp := Real.sqrt_pos.mpr hx
  have hs := Real.sq_sqrt hx.le
  apply (le_div_iff₀ hp).mpr
  have hsq : (Real.sqrt (1-x^2)*(1+x^2/2))^2 ≤ 1 := by
    calc
      _ = (1-x^2)*(1+x^2/2)^2 := by rw [mul_pow,hs]
      _ ≤ 1 := by nlinarith [sq_nonneg (x^2), mul_nonneg (sq_nonneg x) (sq_nonneg (x^2))]
  have hprod : 0 ≤ Real.sqrt (1-x^2)*(1+x^2/2) := by positivity
  nlinarith

theorem actual_arcsin_cubic_lower {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    x + x^3/6 ≤ Real.arcsin x := by
  let f : ℝ → ℝ := fun y => Real.arcsin y-y-y^3/6
  have hd : ∀ y ∈ Icc 0 x, HasDerivAt f (1 / Real.sqrt (1-y^2)-1-y^2/2) y := by
    intro y hy
    have ha := Real.hasDerivAt_arcsin (by linarith [hy.1] : y ≠ -1) (by linarith [hy.2] : y ≠ 1)
    convert! (ha.sub (hasDerivAt_id y)).sub (((hasDerivAt_id y).pow 3).div_const 6) using 1
    simp only [id_eq]
    ring
  have hc : ContinuousOn f (Icc 0 x) := by
    unfold f
    fun_prop
  have hm : MonotoneOn f (Icc 0 x) := monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hc
    (by intro y hy; exact (hd y (interior_subset hy)).differentiableAt.differentiableWithinAt)
    (by intro y hy; rw [(hd y (interior_subset hy)).deriv]
        have hmem := interior_subset hy
        have hh := actual_arcsin_derivative_lower hmem.1 (lt_of_le_of_lt hmem.2 h1)
        linarith)
  have he : f 0 ≤ f x := hm ⟨le_rfl,h0⟩ ⟨h0,le_rfl⟩ h0
  dsimp [f] at he
  rw [Real.arcsin_zero] at he
  linarith

theorem actual_arcsin_sixteenth_upper : Real.arcsin (1/16 : ℝ) < 1/15 := by
  have hp := Real.arcsin_pos.mpr (by norm_num : (0 : ℝ) < 1/16)
  have hlt := Real.arcsin_lt_pi_div_two.mpr (by norm_num : (1/16 : ℝ) < 1)
  have ht := Real.lt_tan hp hlt
  rw [Real.tan_arcsin] at ht
  have hsq : Real.sqrt (1-(1/16 : ℝ)^2)^2 = (255/256 : ℝ) := by
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have hn : 0 ≤ Real.sqrt (1-(1/16 : ℝ)^2) := Real.sqrt_nonneg _
  have hs : (15/16 : ℝ) < Real.sqrt (1-(1/16 : ℝ)^2) := by nlinarith
  have hd : (1/16 : ℝ) / Real.sqrt (1-(1/16 : ℝ)^2) < 1/15 := by
    apply (div_lt_iff₀ (by nlinarith : 0 < Real.sqrt (1-(1/16 : ℝ)^2))).mpr
    nlinarith
  exact ht.trans hd

theorem actual_uniform_cosine_gt_sixteenth :
    (1/16 : ℝ) < Real.sqrt (1-(Root 4)^2) := by
  let t : ℝ := Real.sqrt (1-(1/16 : ℝ)^2)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t^2 = (255/256 : ℝ) := by
    dsimp [t]
    rw [Real.sq_sqrt (by norm_num)]
    norm_num
  have ht1 : t < 1 := by nlinarith
  have ht99 : (99/100 : ℝ) < t := by nlinarith
  have ht3 : (97/100 : ℝ) < t^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ht99.le) (sub_nonneg.mpr ht99.le)]
  have harc : Real.arcsin t = Real.pi/2 - Real.arcsin (1/16 : ℝ) := by
    exact (Real.arccos_eq_arcsin (by norm_num : (0 : ℝ) ≤ 1/16)).symm
  have h1 := actual_arcsin_cubic_lower (x := t/2) (by positivity) (by nlinarith)
  have h2 := actual_arcsin_lower (x := t/4) (by positivity) (by nlinarith)
  have h3 := actual_arcsin_lower (x := t/8) (by positivity) (by nlinarith)
  have hbalance : 2 * Real.pi < Balance 4 t := by
    norm_num [Balance,Delta,Finset.sum_Ico_eq_sum_range,Finset.sum_range_succ]
    rw [harc]
    nlinarith [actual_arcsin_sixteenth_upper, Real.pi_lt_d4]
  have hr := actual_root_spec (by omega : 4 ≤ 4)
  have hroot : Root 4 < t := by
    by_contra hh
    have hm := (actual_balance_strictMono 4).monotoneOn
      ⟨ht0,ht1.le⟩ hr.1 (le_of_not_gt hh)
    linarith [hr.2]
  have hrint := actual_root_interval (by omega : 4 ≤ 4)
  have hs := Real.sq_sqrt (show 0 ≤ 1-(Root 4)^2 by nlinarith [hrint.1,hrint.2])
  have hn := Real.sqrt_nonneg (1-(Root 4)^2)
  nlinarith [hrint.1]
end Reference.MD06CycleProfile
