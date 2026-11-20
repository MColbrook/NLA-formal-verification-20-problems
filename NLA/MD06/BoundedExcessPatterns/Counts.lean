module

public import NLA.MD06.BoundedExcessPatterns.Definitions
public import NLA.MD06.MixedPatternShapes.FiniteShapes
public import NLA.MD06.BadSupportEnumeration.VertexCounts
public import NLA.MD06.PatternUnions.UnionBounds
public import NLA.MD06.WeightedOverlap.PartLimits
public import NLA.MD06.CubicConfiguration.UniformLaw

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06BoundedExcess
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06JointSupportCounts
open Reference.MD06MixedPatternShapes Reference.MD06BadSupportEnumeration
open Reference.MD06PatternUnions Reference.MD06FiniteProbability Reference.MD06WeightedOverlap
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_constraint_card_bound (n v e : ℕ) :
    Fintype.card (ConstraintDatum n v e)≤n^v*2^(9*v^2) := by
  let f : ConstraintDatum n v e →
      (Σ S : {S : Finset (Fin n) // S.card=v},ConstraintOn S.val) :=
    fun P => ⟨⟨VertexSupport P.val,P.property.1⟩,⟨P.val,Finset.Subset.refl _⟩⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun z => z.2.val) h
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at hc
  have hs : (∑S : {S : Finset (Fin n) // S.card=v},Fintype.card (ConstraintOn S.val))=
      n.choose v*2^(9*v^2) := by
    calc
      _ = ∑S : {S : Finset (Fin n) // S.card=v},2^(9*v^2) := by
        apply Finset.sum_congr rfl
        intro S _
        rw [actual_supported_constraint_card,S.property]
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,actual_vertex_sets_card,nsmul_eq_mul,Nat.cast_id]
  rw [hs] at hc
  exact hc.trans (Nat.mul_le_mul_right _ (Nat.choose_le_pow n v))

theorem actual_constraint_count_product (n v e : ℕ) :
    ConstraintCount n v e*PairingDenominator n e=
      Fintype.card (ConstraintDatum n v e)*Fintype.card (Pairing n) := by
  exact actual_pattern_family_sum_product e
    (fun P : ConstraintDatum n v e => P.val)
    (fun P => P.property.2.1)
    (fun P => P.property.2.2.1)
    (fun P => P.property.2.2.2)

theorem actual_constraint_mean_nonnegative (n v e : ℕ) :
    0≤ConstraintMean n v e := by
  unfold ConstraintMean
  positivity

theorem actual_constraint_mean_exact (k v e : ℕ) :
    ConstraintMean (Size k) v e=
      (Fintype.card (ConstraintDatum (Size k) v e) : ℝ)/
        (PairingDenominator (Size k) e : ℝ) := by
  by_cases hi : Nonempty (ConstraintDatum (Size k) v e)
  · obtain ⟨P⟩ := hi
    let : Nonempty (Pairing (Size k)) := actual_pairing_nonempty k
    have ht : (Fintype.card (Pairing (Size k)) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
    have hd : (PairingDenominator (Size k) e : ℝ)≠0 := by
      have h := actual_disjoint_pattern_denominator_ne_zero k P.val
        P.property.2.2.1 P.property.2.2.2
      rw [P.property.2.1] at h
      exact_mod_cast h
    unfold ConstraintMean
    apply (div_eq_div_iff ht hd).mpr
    exact_mod_cast actual_constraint_count_product (Size k) v e
  · let : IsEmpty (ConstraintDatum (Size k) v e) := ⟨fun P => hi ⟨P⟩⟩
    simp [ConstraintMean,ConstraintCount]

theorem actual_constraint_mean_finite_bound (k v e : ℕ) :
    ConstraintMean (Size k) v e≤
      ((Size k : ℝ)^v*(2^(9*v^2) : ℕ))/(PairingDenominator (Size k) e : ℝ) := by
  rw [actual_constraint_mean_exact]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast actual_constraint_card_bound (Size k) v e
  · positivity

theorem actual_excess_constraint_mean_limit (v e : ℕ) (hve : v<e) :
    Tendsto (fun k => ConstraintMean (Size k) v e) atTop (𝓝 0) := by
  have h := (actual_excess_denominator_formula_limit v e hve).mul_const ((2^(9*v^2) : ℕ) : ℝ)
  simp only [zero_mul] at h
  have hr : Tendsto (fun k =>
      ((Size k : ℝ)^v*(2^(9*v^2) : ℕ))/(PairingDenominator (Size k) e : ℝ)) atTop (𝓝 0) := by
    have hh := h.comp actual_size_tendsto_atTop
    convert hh using 1
    funext k
    simp only [Function.comp_apply]
    ring
  exact squeeze_zero (fun k => actual_constraint_mean_nonnegative (Size k) v e)
    (fun k => actual_constraint_mean_finite_bound k v e) hr

#print axioms actual_constraint_card_bound
#print axioms actual_constraint_count_product
#print axioms actual_constraint_mean_nonnegative
#print axioms actual_constraint_mean_exact
#print axioms actual_constraint_mean_finite_bound
#print axioms actual_excess_constraint_mean_limit
end Reference.MD06BoundedExcess
