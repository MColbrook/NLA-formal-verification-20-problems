module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Literal entry error sublevels are bounded; no optimizer or compactness oracle. -/
public import NLA.TR04.TensorOptimumAttainment.ClosedFeasible
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.TensorOptimumAttainment
noncomputable section
open Reference.RecursiveTensorCompletion Reference.TensorCandidateSelection
open scoped BigOperators Matrix Matrix.Norms.Elementwise

theorem continuous_actual_error {m : ℕ} {ns : List ℕ} (A : Tensor m ns) :
    Continuous (error A) := by
  unfold error tensorFrobeniusSq
  fun_prop

theorem actual_entry_sq_le_error {m : ℕ} {ns : List ℕ} (A Y : Tensor m ns)
    (i : Fin m) (j : ModeIndex ns) : (A i j-Y i j)^2 ≤ error A Y := by
  unfold error tensorFrobeniusSq
  calc
    _ ≤ ∑ j', (A i j'-Y i j')^2 :=
      Finset.single_le_sum (fun j' _ => sq_nonneg (A i j'-Y i j')) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', (A i' j'-Y i' j')^2 :=
      Finset.single_le_sum (fun i' _ => Finset.sum_nonneg (fun j' _ => sq_nonneg (A i' j'-Y i' j')))
        (Finset.mem_univ i)

theorem actual_error_sublevel_in_closedBall {m : ℕ} {ns : List ℕ} (A Y : Tensor m ns)
    (h : error A Y ≤ error A 0) :
    Y ∈ Metric.closedBall A (error A 0+1) := by
  have he : 0≤error A 0 := tensorFrobeniusSq_nonneg _
  have hR : 0≤error A 0+1 := by linarith
  rw [Metric.mem_closedBall,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hR).mpr
  intro j
  change ‖Y i j-A i j‖≤error A 0+1
  rw [Real.norm_eq_abs]
  have hs := (actual_entry_sq_le_error A Y i j).trans h
  have heq : (A i j-Y i j)^2=(Y i j-A i j)^2 := by ring
  rw [heq,← sq_abs] at hs
  by_contra hnot
  have hlarge : error A 0+1 < |Y i j-A i j| := lt_of_not_ge hnot
  nlinarith [abs_nonneg (Y i j-A i j)]

#print axioms continuous_actual_error
#print axioms actual_error_sublevel_in_closedBall
end
end Reference.TensorOptimumAttainment
