module

public import NLA.MD06.CombinedDescendingMoments.OverlapCounts
public import NLA.MD06.CombinedDescendingMoments.WeightSeries
public import NLA.MD06.MixedWeightedOverlap.TotalCounts

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedWeightedOverlap Reference.MD06CubicConfiguration
open Reference.MD06FiniteProbability
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_mean_overlap_joint_nonnegative (n q ell : ℕ) :
    0≤MeanOverlapJoint n q ell := by
  unfold MeanOverlapJoint
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (Nat.cast_nonneg _)

theorem actual_mean_overlap_joint_le (n q ell : ℕ) :
    MeanOverlapJoint n q ell≤MeanOverlap n q ell := by
  unfold MeanOverlapJoint MeanOverlap
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro p _
  exact_mod_cast actual_overlap_joint_count_le q ell p

theorem actual_mean_overlap_joint_limit (q ell : ℕ) :
    Tendsto (fun k => MeanOverlapJoint (Size k) q ell) atTop (𝓝 0) := by
  exact squeeze_zero (fun k => actual_mean_overlap_joint_nonnegative (Size k) q ell)
    (fun k => actual_mean_overlap_joint_le (Size k) q ell)
    (actual_mixed_weighted_overlap_mean_limit q ell)

theorem actual_mean_descending_disjoint_overlap (n q ell : ℕ) (hell : 3≤ell) :
    MeanDescending n q ell=MeanDisjointMarked n q ell+MeanOverlapJoint n q ell := by
  rw [actual_mean_descending_as_joint]
  unfold MeanJoint MeanDisjointMarked MeanOverlapJoint
  simp only [actual_joint_count_disjoint_overlap q ell hell,Nat.cast_add,Finset.sum_add_distrib]
  exact add_div _ _ _

theorem actual_combined_descending_moment_limit (q ell : ℕ) (hell : 3≤ell) :
    Tendsto (fun k => MeanDescending (Size k) q ell) atTop
      (𝓝 ((2+(2 : ℝ)^ell/(2*(ell : ℝ)))^q)) := by
  have h := (actual_mean_disjoint_marked_limit q ell (by omega)).add
    (actual_mean_overlap_joint_limit q ell)
  simpa only [←actual_mean_descending_disjoint_overlap _ q ell hell,add_zero] using h

#print axioms actual_mean_overlap_joint_nonnegative
#print axioms actual_mean_overlap_joint_le
#print axioms actual_mean_overlap_joint_limit
#print axioms actual_mean_descending_disjoint_overlap
#print axioms actual_combined_descending_moment_limit
end Reference.MD06CombinedMoments
