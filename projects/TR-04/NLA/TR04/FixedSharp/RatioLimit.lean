module

public import NLA.TR04.FixedSharp.Optimum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
Ratio and limiting-parameter calculations for the literal fixed tensor family.
This module does not identify greedyCandidate with an algorithm output.
That correspondence must be proved in the separate algorithm bridge.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace NLA.TR04.FixedSharp

theorem actual_candidate_ratio (α β γ : ℝ) (hαγ : γ ^ 2 ≤ α ^ 2)
    (hγ : γ ≠ 0) :
    normSq (family α β γ - greedyCandidate α) / optimalError (family α β γ) =
      1 + (β / γ) ^ 2 := by
  rw [actual_greedy_candidate_error, actual_optimal_error α β γ hαγ]
  field_simp [hγ] <;> ring

def sharpGamma (n : ℕ) : ℝ := 1 + 1 / ((n : ℝ) + 2)

theorem sharpGamma_bounds (n : ℕ) : 1 < sharpGamma n ∧ sharpGamma n < 2 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hp : 0 < 1 / ((n : ℝ) + 2) := by positivity
  have hu : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one hd).2 (by linarith)
  dsimp [sharpGamma]
  constructor <;> linarith

theorem sharpGamma_tendsto_one : Tendsto sharpGamma atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hn.eventually_ge_atTop b] with n hnb
    linarith
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hd
  change Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 2)) atTop (𝓝 1)
  simpa only [add_zero] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add hi)

theorem sharp_family_candidate_ratio (n : ℕ) :
    normSq (family 2 1 (sharpGamma n) - greedyCandidate 2) /
        optimalError (family 2 1 (sharpGamma n)) =
      1 + (1 / sharpGamma n) ^ 2 := by
  have hb := sharpGamma_bounds n
  exact actual_candidate_ratio 2 1 (sharpGamma n) (by nlinarith) (by linarith)

theorem sharp_family_candidate_ratio_tendsto_two :
    Tendsto (fun n : ℕ =>
      normSq (family 2 1 (sharpGamma n) - greedyCandidate 2) /
        optimalError (family 2 1 (sharpGamma n))) atTop (𝓝 2) := by
  have hi : Tendsto (fun n : ℕ => (1 : ℝ) / sharpGamma n) atTop (𝓝 (1 / 1)) :=
    tendsto_const_nhds.div sharpGamma_tendsto_one (by norm_num)
  have hr : Tendsto (fun n : ℕ => 1 + (1 / sharpGamma n) ^ 2)
      atTop (𝓝 (1 + (1 / 1 : ℝ) ^ 2)) :=
    tendsto_const_nhds.add (hi.pow 2)
  simp_rw [sharp_family_candidate_ratio]
  convert hr using 1 <;> norm_num

#print axioms actual_candidate_ratio
#print axioms sharpGamma_bounds
#print axioms sharpGamma_tendsto_one
#print axioms sharp_family_candidate_ratio
#print axioms sharp_family_candidate_ratio_tendsto_two

end NLA.TR04.FixedSharp
