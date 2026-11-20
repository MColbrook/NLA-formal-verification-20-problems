module

public import NLA.IE21.FiniteTrimming
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace NLA.IE21.LiteralWrappers

theorem positive_part_hasDerivAt (y t : ℝ) (ht : t ≠ y) :
    HasDerivAt (fun s => max (s-y) 0) (if y < t then 1 else 0) t := by
  rcases lt_or_gt_of_ne ht with hlt | hgt
  · have he : (fun s : ℝ => max (s-y) 0) =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds hlt] with s hs
      exact max_eq_right (sub_nonpos.mpr hs.le)
    simpa [not_lt_of_gt hlt] using (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he
  · have he : (fun s : ℝ => max (s-y) 0) =ᶠ[𝓝 t] fun s => s-y := by
      filter_upwards [eventually_gt_nhds hgt] with s hs
      exact max_eq_left (sub_nonneg.mpr hs.le)
    simpa [hgt] using ((hasDerivAt_id t).sub_const y).congr_of_eventuallyEq he

/-- The actual slope between observations, including ties in the data. -/
theorem trimDual_hasDerivAt {m : ℕ} (k : ℕ) (y : Fin m → ℝ) (t : ℝ)
    (ht : ∀ i, t ≠ y i) :
    HasDerivAt (trimDual k y)
      ((k : ℝ) / m - ((Finset.univ.filter (fun i => y i < t)).card : ℝ) / m) t := by
  classical
  have hh := (HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => positive_part_hasDerivAt (y i) t (ht i))).const_mul (1 / (m : ℝ))
  have hs : (∑ i : Fin m, if y i < t then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i => y i < t)).card : ℝ) := by simp
  have h := ((hasDerivAt_id t).const_mul ((k : ℝ)/m)).sub hh
  convert h using 1 <;> first | rfl | (simp [hs]; ring)

#print axioms trimDual_hasDerivAt

theorem trimDual_slope_signs {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (y : Fin m → ℝ) (t : ℝ)
    (ht : ∀ i, t ≠ y i) :
    ((Finset.univ.filter (fun i => y i < t)).card < k ↔ 0 < deriv (trimDual k y) t) ∧
    ((Finset.univ.filter (fun i => y i < t)).card = k ↔ deriv (trimDual k y) t = 0) ∧
    (k < (Finset.univ.filter (fun i => y i < t)).card ↔ deriv (trimDual k y) t < 0) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [(trimDual_hasDerivAt k y t ht).deriv]
  have hc : ((Finset.univ.filter (fun i => y i < t)).card : ℝ) / m < (k : ℝ)/m ↔
      (Finset.univ.filter (fun i => y i < t)).card < k := by
    rw [div_lt_div_iff_of_pos_right hm0]
    exact_mod_cast Iff.rfl
  have he : (k : ℝ)/m = ((Finset.univ.filter (fun i => y i < t)).card : ℝ)/m ↔
      (Finset.univ.filter (fun i => y i < t)).card = k := by
    rw [div_left_inj' hm0.ne']
    exact_mod_cast eq_comm
  have hl : (k : ℝ)/m < ((Finset.univ.filter (fun i => y i < t)).card : ℝ)/m ↔
      k < (Finset.univ.filter (fun i => y i < t)).card := by
    rw [div_lt_div_iff_of_pos_right hm0]
    exact_mod_cast Iff.rfl
  exact ⟨by simpa only [sub_pos] using hc.symm,
    by simpa only [sub_eq_zero] using he.symm,
    by simpa only [sub_neg] using hl.symm⟩

#print axioms trimDual_slope_signs
end NLA.IE21.LiteralWrappers
