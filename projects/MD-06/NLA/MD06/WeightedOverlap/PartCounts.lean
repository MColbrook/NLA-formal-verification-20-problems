module

public import NLA.MD06.WeightedOverlap.Definitions
public import NLA.MD06.BadSupportEnumeration.VertexCounts
public import NLA.MD06.BadOverlapExcess.Excess
public import NLA.MD06.PatternUnions.UnionBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WeightedOverlap
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
open Reference.MD06BadJointMoments Reference.MD06JointSupportCounts
open Reference.MD06PairingCounts Reference.MD06BadSupportEnumeration
open Reference.MD06BadOverlap Reference.MD06PatternUnions Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_part_card_bound (n q v e : ℕ) :
    Fintype.card (PartDatum n q v e) ≤ n^v*(3*v+18*v^2)^q := by
  let forget : PartDatum n q v e →
      {f : JointDatum n q // (VertexSupport (JointPattern f)).card = v} :=
    fun f => ⟨f.val,f.property.1⟩
  have hi : Function.Injective forget := by
    intro f g h
    apply Subtype.ext
    exact congrArg (fun z : {f : JointDatum n q //
      (VertexSupport (JointPattern f)).card = v} => z.val) h
  exact (Fintype.card_le_of_injective forget hi).trans
    (actual_joint_given_vertex_count_power_bound n q v)

theorem actual_part_shape_bounds {n q v e : ℕ} (f : PartDatum n q v e) :
    v+1 ≤ e ∧ e ≤ 2*q := by
  obtain ⟨p,hp⟩ := f.property.2.2.2
  have h := actual_overlapping_joint_support_bound f.val p hp f.property.2.2.1
  simpa only [f.property.1,f.property.2.1] using h

theorem actual_part_disjoint_endpoints {n q v e : ℕ} (f : PartDatum n q v e) :
    ∀ x ∈ JointPattern f.val, ∀ y ∈ JointPattern f.val, x ≠ y →
      Disjoint ({x.1,x.2} : Finset (Dart n)) {y.1,y.2} := by
  obtain ⟨p,hp⟩ := f.property.2.2.2
  exact actual_joint_matching_disjoint_endpoints f.val p hp

theorem actual_part_count_product (n q v e : ℕ) :
    PartCount n q v e * PairingDenominator n e =
      Fintype.card (PartDatum n q v e) * Fintype.card (Pairing n) := by
  exact actual_pattern_family_sum_product e
    (fun f : PartDatum n q v e => JointPattern f.val)
    (fun f => f.property.2.1)
    (fun f => actual_joint_pattern_distinct_endpoints f.val)
    actual_part_disjoint_endpoints

theorem actual_part_mean_nonnegative (n q v e : ℕ) : 0 ≤ PartMean n q v e := by
  unfold PartMean
  positivity

theorem actual_part_mean_exact (k q v e : ℕ) :
    PartMean (Size k) q v e =
      (Fintype.card (PartDatum (Size k) q v e) : ℝ) /
        (PairingDenominator (Size k) e : ℝ) := by
  by_cases hi : Nonempty (PartDatum (Size k) q v e)
  · obtain ⟨f⟩ := hi
    have ht : (Fintype.card (Pairing (Size k)) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
    have hd : (PairingDenominator (Size k) e : ℝ) ≠ 0 := by
      have h := actual_disjoint_pattern_denominator_ne_zero k (JointPattern f.val)
        (actual_joint_pattern_distinct_endpoints f.val) (actual_part_disjoint_endpoints f)
      rw [f.property.2.1] at h
      exact_mod_cast h
    unfold PartMean
    apply (div_eq_div_iff ht hd).mpr
    exact_mod_cast actual_part_count_product (Size k) q v e
  · let : IsEmpty (PartDatum (Size k) q v e) := ⟨fun f => hi ⟨f⟩⟩
    simp [PartMean,PartCount]

theorem actual_part_mean_finite_bound (k q v e : ℕ) :
    PartMean (Size k) q v e ≤
      ((Size k : ℝ)^v*(3*v+18*v^2)^q) /
        (PairingDenominator (Size k) e : ℝ) := by
  rw [actual_part_mean_exact]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast actual_part_card_bound (Size k) q v e
  · positivity

#print axioms actual_part_card_bound
#print axioms actual_part_shape_bounds
#print axioms actual_part_disjoint_endpoints
#print axioms actual_part_count_product
#print axioms actual_part_mean_nonnegative
#print axioms actual_part_mean_exact
#print axioms actual_part_mean_finite_bound
end Reference.MD06WeightedOverlap
