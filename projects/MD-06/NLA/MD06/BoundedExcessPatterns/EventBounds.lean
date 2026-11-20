module

public import NLA.MD06.BoundedExcessPatterns.EventDefinitions
public import NLA.MD06.BoundedExcessPatterns.Counts

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06BoundedExcess
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06FiniteProbability
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_bounded_excess_event_card_le (n K : ℕ) :
    Fintype.card {p : Pairing n // HasBoundedExcess K p}≤TotalConstraintCount n K := by
  let f : {p : Pairing n // HasBoundedExcess K p} →
      (ΣC : BoundedDatum n K,{p : Pairing n // Matches C.2.val p}) :=
    fun p => ⟨Classical.choose p.property,⟨p.val,Classical.choose_spec p.property⟩⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z => z.2.val) h
  have hc := Fintype.card_le_of_injective f hf
  let E : (ΣC : BoundedDatum n K,{p : Pairing n // Matches C.2.val p}) ≃
      (Σs : ExcessShape K,ΣP : ConstraintDatum n s.val.1.val s.val.2.val,
        {p : Pairing n // Matches P.val p}) :=
    { toFun := fun x => ⟨x.1.1,x.1.2,x.2⟩
      invFun := fun x => ⟨⟨x.1,x.2.1⟩,x.2.2⟩
      left_inv := by rintro ⟨⟨s,P⟩,p⟩;rfl
      right_inv := by rintro ⟨s,P,p⟩;rfl }
  have he : Fintype.card (ΣC : BoundedDatum n K,{p : Pairing n // Matches C.2.val p})=
      TotalConstraintCount n K := by
    rw [Fintype.card_congr E,Fintype.card_sigma]
    simp only [Fintype.card_sigma,TotalConstraintCount,ConstraintCount,PatternCount]
  exact hc.trans (le_of_eq he)

theorem actual_total_constraint_mean_shape_sum (n K : ℕ) :
    TotalConstraintMean n K=
      ∑s : ExcessShape K,ConstraintMean n s.val.1.val s.val.2.val := by
  simp only [TotalConstraintMean,TotalConstraintCount,ConstraintMean,Nat.cast_sum,Finset.sum_div]

theorem actual_total_constraint_mean_limit (K : ℕ) :
    Tendsto (fun k => TotalConstraintMean (Size k) K) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (ExcessShape K))
    (fun s _ => actual_excess_constraint_mean_limit s.val.1.val s.val.2.val s.property)
  simpa only [actual_total_constraint_mean_shape_sum,Finset.sum_const_zero] using h

theorem actual_excess_probability_nonnegative (k K : ℕ) :
    0≤ExcessProbability k K := by
  unfold ExcessProbability PairingProbability
  positivity

theorem actual_excess_probability_le_mean (k K : ℕ) :
    ExcessProbability k K≤TotalConstraintMean (Size k) K := by
  unfold ExcessProbability PairingProbability TotalConstraintMean
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast actual_bounded_excess_event_card_le (Size k) K

theorem actual_bounded_excess_probability_limit (K : ℕ) :
    Tendsto (fun k => ExcessProbability k K) atTop (𝓝 0) := by
  exact squeeze_zero (fun k => actual_excess_probability_nonnegative k K)
    (fun k => actual_excess_probability_le_mean k K) (actual_total_constraint_mean_limit K)

#print axioms actual_bounded_excess_event_card_le
#print axioms actual_total_constraint_mean_shape_sum
#print axioms actual_total_constraint_mean_limit
#print axioms actual_excess_probability_nonnegative
#print axioms actual_excess_probability_le_mean
#print axioms actual_bounded_excess_probability_limit
end Reference.MD06BoundedExcess
