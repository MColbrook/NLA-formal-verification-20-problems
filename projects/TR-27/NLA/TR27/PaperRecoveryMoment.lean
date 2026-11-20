module

public import NLA.TR27.PaperRationalDefinitions
public import NLA.TR27.PaperIntegralIdentity

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

theorem recovery_real_moment_ne_zero {r : ℕ} (hr : 2 ≤ r) :
    chosenPowerSumReal r 2 * chosenPowerSumReal r 4 - chosenPowerSumReal r 3^2 ≠ 0 := by
  intro hdet
  let s2 := chosenPowerSumReal r 2
  let s3 := chosenPowerSumReal r 3
  have hsum :
      (∑ i : Fin r, (s2*((i.val+1 : ℕ) : ℝ)^2 - s3*((i.val+1 : ℕ) : ℝ))^2) =
        s2^2 * chosenPowerSumReal r 4 - (2*s2*s3)*chosenPowerSumReal r 3 +
          s3^2 * chosenPowerSumReal r 2 := by
    calc
      _ = ∑ i : Fin r, (s2^2*((i.val+1 : ℕ) : ℝ)^4 -
          (2*s2*s3)*((i.val+1 : ℕ) : ℝ)^3 + s3^2*((i.val+1 : ℕ) : ℝ)^2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
  have hz : (∑ i : Fin r, (s2*((i.val+1 : ℕ) : ℝ)^2 - s3*((i.val+1 : ℕ) : ℝ))^2) = 0 := by
    rw [hsum]
    dsimp only [s2, s3]
    linear_combination (chosenPowerSumReal r 2)*hdet
  have hterm (i : Fin r) : s2*((i.val+1 : ℕ) : ℝ)^2 - s3*((i.val+1 : ℕ) : ℝ) = 0 := by
    apply eq_zero_of_pow_eq_zero
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg
      (s2*((j.val+1 : ℕ) : ℝ)^2 - s3*((j.val+1 : ℕ) : ℝ)))).mp hz i (Finset.mem_univ _)
  have h1 := hterm ⟨0, by omega⟩
  have h2 := hterm ⟨1, by omega⟩
  norm_num at h1 h2
  have hlow := Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin r => ((i.val+1 : ℕ) : ℝ)^2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ (⟨0, by omega⟩ : Fin r))
  have hlow' : (1 : ℝ) ≤ s2 := by
    simpa [s2, chosenPowerSumReal] using hlow
  nlinarith

theorem recoveryMomentC_ne_zero {r : ℕ} (hr : 2 ≤ r) : recoveryMomentC r ≠ 0 := by
  have h := recovery_real_moment_ne_zero hr
  rw [recoveryMomentC, ← chosenPowerSum_cast r 2, ← chosenPowerSum_cast r 4,
    ← chosenPowerSum_cast r 3]
  exact_mod_cast h

#print axioms recoveryMomentC_ne_zero
end NLA.TR27.Paper
