module

public import NLA.MF05.PaperCyclicRadius
public import NLA.MF05.PaperCyclicDistance
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace NLA.MF05.Paper.Cyclic

theorem exponent_obstruction (n : ℕ) (α C ε : ℝ)
    (hα : 1 / ((n+1 : ℕ) : ℝ) < α) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      realHausdorff {shift n} {perturbation n δ} < ε ∧
      C * (realHausdorff {shift n} {perturbation n δ}) ^ α <
        |realRadius {perturbation n δ} - realRadius {shift n}| := by
  let p : ℝ := ((n+1 : ℕ) : ℝ) * α - 1
  have hd : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have hp : 0 < p := by
    have := (div_lt_iff₀ hd).mp hα
    dsimp [p]
    nlinarith
  have ht : Tendsto (fun r : ℝ => C * r^p) (𝓝[>] 0) (𝓝 0) := by
    have hh := ((Real.continuous_rpow_const hp.le).continuousAt (x := (0 : ℝ))).tendsto
    have hh' : Tendsto (fun r : ℝ => r^p) (𝓝[>] 0) (𝓝 0) := by
      convert! hh.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left) using 1 <;>
        simp [Real.zero_rpow hp.ne']
    simpa using hh'.const_mul C
  have hs : ∀ᶠ r : ℝ in 𝓝[>] 0, C*r^p < 1 := ht.eventually (gt_mem_nhds (by norm_num))
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0, r < min ε 1 :=
    (eventually_lt_nhds (lt_min hε zero_lt_one)).filter_mono inf_le_left
  have hz : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r, hr, hsmall, hbound⟩ := (hz.and (he.and hs)).exists
  have hr1 : r ≤ 1 := (lt_min_iff.mp hsmall).2.le
  have hrε : r < ε := (lt_min_iff.mp hsmall).1
  have hpow : r^(n+1) ≤ r := by
    calc
      r^(n+1) = r^n * r := pow_succ _ _
      _ ≤ 1*r := mul_le_mul_of_nonneg_right (pow_le_one₀ hr.le hr1) hr.le
      _ = r := one_mul _
  refine ⟨r^(n+1), pow_pos hr _, hpow.trans hr1, ?_, ?_⟩
  · rw [perturbation_distance, abs_of_pos (pow_pos hr _)]
    exact hpow.trans_lt hrε
  · rw [perturbation_distance, abs_of_pos (pow_pos hr _), perturbation_radius n r hr,
      shift_radius_zero, sub_zero, abs_of_pos hr]
    have heq : (r^(n+1))^α = r * r^p := by
      rw [← Real.rpow_natCast_mul hr.le]
      have hxp : ((n+1 : ℕ) : ℝ) * α = 1+p := by dsimp [p]; ring
      rw [hxp, Real.rpow_add hr, Real.rpow_one]
    rw [heq]
    nlinarith [mul_lt_mul_of_pos_left hbound hr]

theorem local_lipschitz_obstruction (n : ℕ) (hn : 1 ≤ n) (C ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      realHausdorff {shift n} {perturbation n δ} < ε ∧
      C * realHausdorff {shift n} {perturbation n δ} <
        |realRadius {perturbation n δ} - realRadius {shift n}| := by
  have hα : 1 / ((n+1 : ℕ) : ℝ) < (1 : ℝ) := by
    apply (div_lt_one (by positivity)).mpr
    exact_mod_cast (show 1 < n+1 by omega)
  simpa only [Real.rpow_one] using exponent_obstruction n 1 C ε hα hε

#print axioms exponent_obstruction
end NLA.MF05.Paper.Cyclic
