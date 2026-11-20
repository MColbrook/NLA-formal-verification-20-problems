module

public import NLA.MD06.DisjointTypedEnumeration.MeanDefinitions
public import NLA.MD06.DisjointTypedEnumeration.PatternGeometry
public import NLA.MD06.BadPatternCounts.FirstMoment
public import NLA.MD06.PatternUnions.UnionBounds
public import NLA.MD06.CycleMoments.FirstLimits
public import NLA.MD06.PairingCounts.PatternProbability

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06CubicConfiguration Reference.MD06JointSupportCounts
open Reference.MD06BadJointMoments Reference.MD06BadPatternCounts Reference.MD06WeightedOverlap
open Reference.MD06BadDisjointDecomposition Reference.MD06PatternUnions
open Reference.MD06PairingCounts Reference.MD06FiniteProbability Reference.MD06CycleMoments
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_typed_count_product {n q : ℕ} (b : Fin q → Bool) :
    (∑ p : Pairing n,TypedCount b p)*PairingDenominator n (Weight b) =
      3^(Weight b)*n.descFactorial (Weight b)*Fintype.card (Pairing n) := by
  have h := actual_pattern_family_sum_product (Weight b)
    (fun f : TypedJoint (n := n) Finset.univ b => JointPattern f.val)
    (actual_typed_joint_pattern_card Finset.univ b)
    (actual_typed_joint_pattern_distinct_endpoints Finset.univ b)
    (actual_typed_joint_pattern_disjoint_endpoints Finset.univ b)
  rw [←actual_family_matching_sum,actual_typed_joint_card] at h
  simpa only [TypedCount,Finset.card_univ,Fintype.card_fin] using h

theorem actual_mean_typed_formula {q : ℕ} (k : ℕ) (b : Fin q → Bool) :
    MeanTyped (Size k) b =
      ((3^(Weight b)*(Size k).descFactorial (Weight b) : ℕ) : ℝ)/
        (PairingDenominator (Size k) (Weight b) : ℝ) := by
  by_cases hf : Nonempty (TypedJoint (n := Size k) Finset.univ b)
  · let f := Classical.choice hf
    have hd : (PairingDenominator (Size k) (Weight b) : ℝ) ≠ 0 := by
      have h := actual_disjoint_pattern_denominator_ne_zero k (JointPattern f.val)
        (actual_typed_joint_pattern_distinct_endpoints Finset.univ b f)
        (actual_typed_joint_pattern_disjoint_endpoints Finset.univ b f)
      rw [actual_typed_joint_pattern_card Finset.univ b f] at h
      exact_mod_cast h
    have ht : (Fintype.card (Pairing (Size k)) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    unfold MeanTyped
    rw [←Nat.cast_sum]
    apply (div_eq_div_iff ht hd).mpr
    exact_mod_cast actual_typed_count_product (n := Size k) b
  · have : IsEmpty (TypedJoint (n := Size k) Finset.univ b) :=
      not_nonempty_iff.mp hf
    have hc : 3^(Weight b)*(Size k).descFactorial (Weight b)=0 := by
      have h := actual_typed_joint_card (Size k) q Finset.univ b
      simpa using h.symm
    simp [MeanTyped,TypedCount,FamilyMatchingCount,hc]

theorem actual_typed_formula_limit (w : ℕ) :
    Tendsto (fun n : ℕ => ((3^w*n.descFactorial w : ℕ) : ℝ)/
      (PairingDenominator n w : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have ht := (actual_normalized_desc_factorial_limit w).div
    (actual_normalized_pairing_denominator_limit w) (by positivity)
  have hm := ht.mul_const ((3 : ℝ)^w)
  have hc : (1/(3 : ℝ)^w)*(3 : ℝ)^w=1 := by field_simp
  rw [hc] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [Pi.div_apply,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp [hn0]

theorem actual_mean_typed_limit {q : ℕ} (b : Fin q → Bool) :
    Tendsto (fun k : ℕ => MeanTyped (Size k) b) atTop (𝓝 (1 : ℝ)) := by
  have hs : Tendsto Size atTop atTop := by
    apply tendsto_atTop.2
    intro a
    filter_upwards [eventually_ge_atTop a] with k hk
    simp only [Size]
    omega
  exact ((actual_typed_formula_limit (Weight b)).comp hs).congr
    (fun k => (actual_mean_typed_formula k b).symm)

#print axioms actual_typed_count_product
#print axioms actual_mean_typed_formula
#print axioms actual_typed_formula_limit
#print axioms actual_mean_typed_limit
end Reference.MD06DisjointTypedEnumeration
