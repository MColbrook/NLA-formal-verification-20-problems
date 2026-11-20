module

public import NLA.MD06.BadPatternCounts.CountDefinitions
public import NLA.MD06.BadPatternCounts.Cardinality
public import NLA.MD06.BadPatternCounts.PatternProperties
public import NLA.MD06.PatternUnions.UnionBounds
public import NLA.MD06.CycleMoments.FirstLimits

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadPatternCounts
open Reference.MD06Simplicity Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06FiniteProbability Reference.MD06PatternUnions Reference.MD06CyclePairPatterns Reference.MD06CycleMoments
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_family_matching_sum {I : Type*} [Fintype I] {n : ℕ}
    (C : I → Finset (Dart n × Dart n)) :
    (∑ p : Pairing n, FamilyMatchingCount C p) = ∑ i : I, PatternCount (C i) := by
  let e : (Σ p : Pairing n, {i : I // Matches (C i) p}) ≃
      (Σ i : I, {p : Pairing n // Matches (C i) p}) :=
    { toFun := fun x => ⟨x.2.val,⟨x.1,x.2.property⟩⟩
      invFun := fun x => ⟨x.2.val,⟨x.1,x.2.property⟩⟩
      left_inv := by rintro ⟨p,i,h⟩; rfl
      right_inv := by rintro ⟨i,p,h⟩; rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma,Fintype.card_sigma] at h
  simpa only [FamilyMatchingCount,PatternCount,← Nat.card_eq_fintype_card] using h

theorem actual_loop_denominator_ne_zero (k : ℕ) :
    PairingDenominator (Size k) 1 ≠ 0 := by
  let d : LoopDatum (Size k) :=
    (⟨0,by simp only [Size];omega⟩,⟨(0,1),by decide⟩)
  have h := actual_disjoint_pattern_denominator_ne_zero k (LoopPattern d)
    (actual_loop_pattern_distinct_endpoints d) (actual_loop_pattern_disjoint_endpoints d)
  rw [actual_loop_pattern_card d] at h
  exact h

theorem actual_double_denominator_ne_zero (k : ℕ) :
    PairingDenominator (Size k) 2 ≠ 0 := by
  let d : DoubleDatum (Size k) :=
    (⟨(⟨0,by simp only [Size];omega⟩,⟨1,by simp only [Size];omega⟩),by change (0 : ℕ) < 1;omega⟩,
      ⟨(0,1),by decide⟩,⟨(0,1),by decide⟩,false)
  have h := actual_disjoint_pattern_denominator_ne_zero k (DoublePattern d)
    (actual_double_pattern_distinct_endpoints d) (actual_double_pattern_disjoint_endpoints d)
  rw [actual_double_pattern_card d] at h
  exact h

theorem actual_mean_loop_count (k : ℕ) :
    MeanLoopCount k = (3 : ℝ)*(Size k : ℝ)/(PairingDenominator (Size k) 1 : ℝ) := by
  have ht : (Fintype.card (Pairing (Size k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hd : (PairingDenominator (Size k) 1 : ℝ) ≠ 0 := by
    exact_mod_cast actual_loop_denominator_ne_zero k
  have h := actual_pattern_family_sum_product 1
    (LoopPattern (n := Size k)) actual_loop_pattern_card
    actual_loop_pattern_distinct_endpoints actual_loop_pattern_disjoint_endpoints
  rw [← actual_family_matching_sum,actual_loop_datum_card] at h
  unfold MeanLoopCount
  simp only [LoopCount,← Nat.cast_sum]
  apply (div_eq_div_iff ht hd).mpr
  exact_mod_cast h

theorem actual_mean_double_count (k : ℕ) :
    MeanDoubleCount k = (18 : ℝ)*((Size k).choose 2 : ℝ)/
      (PairingDenominator (Size k) 2 : ℝ) := by
  have ht : (Fintype.card (Pairing (Size k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hd : (PairingDenominator (Size k) 2 : ℝ) ≠ 0 := by
    exact_mod_cast actual_double_denominator_ne_zero k
  have h := actual_pattern_family_sum_product 2
    (DoublePattern (n := Size k)) actual_double_pattern_card
    actual_double_pattern_distinct_endpoints actual_double_pattern_disjoint_endpoints
  rw [← actual_family_matching_sum,actual_double_datum_card] at h
  unfold MeanDoubleCount
  simp only [DoubleCount,← Nat.cast_sum]
  apply (div_eq_div_iff ht hd).mpr
  exact_mod_cast h

theorem actual_bad_count_sum {n : ℕ} (p : Pairing n) :
    BadCount p = LoopCount p + DoubleCount p := by
  let e : {z : BadDatum n // Matches (BadPattern z) p} ≃
      ({z : LoopDatum n // Matches (LoopPattern z) p} ⊕
        {z : DoubleDatum n // Matches (DoublePattern z) p}) :=
    { toFun := fun z => match z with
        | ⟨.inl x,h⟩ => .inl ⟨x,h⟩
        | ⟨.inr x,h⟩ => .inr ⟨x,h⟩
      invFun := fun z => match z with
        | .inl ⟨x,h⟩ => ⟨.inl x,h⟩
        | .inr ⟨x,h⟩ => ⟨.inr x,h⟩
      left_inv := by rintro ⟨z,h⟩; cases z <;> rfl
      right_inv := by intro z; cases z <;> rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sum] at h
  simpa only [BadCount,LoopCount,DoubleCount,FamilyMatchingCount,
    ← Nat.card_eq_fintype_card] using h

theorem actual_mean_bad_count_sum (k : ℕ) :
    MeanBadCount k = MeanLoopCount k + MeanDoubleCount k := by
  unfold MeanBadCount MeanLoopCount MeanDoubleCount
  simp only [actual_bad_count_sum,Nat.cast_add,Finset.sum_add_distrib,add_div]

theorem actual_mean_loop_cycle_binding (k : ℕ) :
    MeanLoopCount k = MeanOrientedCycles k 1 / 2 := by
  rw [actual_mean_loop_count,actual_mean_oriented_cycles_formula]
  simp only [Nat.descFactorial_one,pow_one]
  ring

theorem actual_mean_double_cycle_binding (k : ℕ) :
    MeanDoubleCount k = MeanOrientedCycles k 2 / 4 := by
  rw [actual_mean_double_count,actual_mean_oriented_cycles_formula,
    Nat.descFactorial_eq_factorial_mul_choose]
  norm_num [Nat.cast_mul]
  ring

theorem actual_mean_loop_count_limit :
    Tendsto MeanLoopCount atTop (𝓝 (1 : ℝ)) := by
  have h := (actual_mean_oriented_cycles_limit 1).div_const 2
  norm_num at h
  exact h.congr (fun k => (actual_mean_loop_cycle_binding k).symm)

theorem actual_mean_double_count_limit :
    Tendsto MeanDoubleCount atTop (𝓝 (1 : ℝ)) := by
  have h := (actual_mean_oriented_cycles_limit 2).div_const 4
  norm_num at h
  exact h.congr (fun k => (actual_mean_double_cycle_binding k).symm)

theorem actual_mean_bad_count_limit :
    Tendsto MeanBadCount atTop (𝓝 (2 : ℝ)) := by
  have h := actual_mean_loop_count_limit.add actual_mean_double_count_limit
  norm_num at h
  exact h.congr (fun k => (actual_mean_bad_count_sum k).symm)

#print axioms actual_family_matching_sum
#print axioms actual_loop_denominator_ne_zero
#print axioms actual_double_denominator_ne_zero
#print axioms actual_mean_loop_count
#print axioms actual_mean_double_count
#print axioms actual_bad_count_sum
#print axioms actual_mean_bad_count_sum
#print axioms actual_mean_loop_cycle_binding
#print axioms actual_mean_double_cycle_binding
#print axioms actual_mean_loop_count_limit
#print axioms actual_mean_double_count_limit
#print axioms actual_mean_bad_count_limit
end Reference.MD06BadPatternCounts