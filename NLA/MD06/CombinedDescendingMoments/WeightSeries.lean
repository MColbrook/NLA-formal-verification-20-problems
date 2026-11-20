module

public import NLA.MD06.CombinedDescendingMoments.WeightDefinitions
public import NLA.MD06.CombinedDescendingMoments.DisjointCounts
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06SupportedCanonicalCycles Reference.MD06FiniteProbability
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_cycle_weight_ratio_product {q : ℕ} (L : Fin q→ℕ) :
    (2 : ℝ)^(CycleWeight L)/(CycleSymmetryFactor L : ℝ)=
      ∏i,(2 : ℝ)^(L i)/(2*(L i : ℝ)) := by
  unfold CycleWeight CycleSymmetryFactor
  simp only [Nat.cast_prod,Nat.cast_mul,Nat.cast_ofNat,
    Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]

theorem actual_tag_weight_sum (ell : ℕ) :
    (∑t : MarkTag,TagWeight ell t)=2+(2 : ℝ)^ell/(2*(ell : ℝ)) := by
  change (∑t∈({.loop,.double,.cycle} : Finset MarkTag),TagWeight ell t)=
    2+(2 : ℝ)^ell/(2*(ell : ℝ))
  rw [Finset.sum_insert (by simp),Finset.sum_insert (by simp),Finset.sum_singleton]
  norm_num [TagWeight,TagLength]
  ring

theorem actual_mixed_leading_constant (q ell : ℕ) :
    LeadingConstant q ell=(2+(2 : ℝ)^ell/(2*(ell : ℝ)))^q := by
  unfold LeadingConstant
  simp_rw [actual_cycle_weight_ratio_product]
  change (∑mask : Fin q→MarkTag,∏i,TagWeight ell (mask i))=
    (2+(2 : ℝ)^ell/(2*(ell : ℝ)))^q
  rw [←Fintype.sum_pow,actual_tag_weight_sum]

theorem actual_mean_disjoint_marked_limit (q ell : ℕ) (hell : 0<ell) :
    Tendsto (fun k => MeanDisjointMarked (Size k) q ell) atTop
      (𝓝 ((2+(2 : ℝ)^ell/(2*(ell : ℝ)))^q)) := by
  have h := actual_mean_disjoint_marked_shape_limit q ell hell
  change Tendsto (fun k => MeanDisjointMarked (Size k) q ell) atTop
    (𝓝 (LeadingConstant q ell)) at h
  rw [actual_mixed_leading_constant] at h
  exact h

#print axioms actual_cycle_weight_ratio_product
#print axioms actual_tag_weight_sum
#print axioms actual_mixed_leading_constant
#print axioms actual_mean_disjoint_marked_limit
end Reference.MD06CombinedMoments
