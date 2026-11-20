module

public import NLA.MD06.MixedLowCycleBijections.LowMaps
public import NLA.MD06.BadPatternCounts.FirstMoment
public import NLA.MD06.BadPatternCounts.PatternProperties
public import NLA.MD06.CanonicalCyclePatterns.FirstLimits

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedLowCycleBijections
open Reference.MD06MixedPatternShapes Reference.MD06CanonicalCyclePatterns
open Reference.MD06Simplicity Reference.MD06BadOverlap Reference.MD06BadPatternCounts
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
open Reference.MD06FiniteProbability
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_canonical_datum_edge_card {n ell : ℕ} (C : CanonicalCycleDatum n ell) :
    C.val.card=ell := by
  obtain ⟨D,hD⟩ := C.property
  rw [←hD]
  exact actual_canonical_cycle_pattern_card D

theorem actual_bad_datum_edge_card_le_two {n : ℕ} (b : BadDatum n) :
    (BadPattern b).card≤2 := by
  cases b with
  | inl L => change (LoopPattern L).card≤2;rw [actual_loop_pattern_card];decide
  | inr D => change (DoublePattern D).card≤2;rw [actual_double_pattern_card]

theorem actual_marked_pattern_injective (n ell : ℕ) (hell : 3≤ell) :
    Function.Injective (@MarkedPattern n ell) := by
  intro x y h
  cases x with
  | inl b =>
    cases y with
    | inl c =>
      change BadPattern b=BadPattern c at h
      exact congrArg Sum.inl (actual_bad_pattern_injective n h)
    | inr C =>
      change BadPattern b=C.val at h
      have hb := actual_bad_datum_edge_card_le_two b
      rw [h,actual_canonical_datum_edge_card] at hb
      omega
  | inr C =>
    cases y with
    | inl b =>
      change C.val=BadPattern b at h
      have hb := actual_bad_datum_edge_card_le_two b
      rw [←h,actual_canonical_datum_edge_card] at hb
      omega
    | inr D =>
      change C.val=D.val at h
      exact congrArg Sum.inr (Subtype.ext h)

theorem actual_marked_matching_count_sum {n ell : ℕ} (p : Pairing n) :
    MarkedMatchingCount (ell:=ell) p=BadCount p+CanonicalCycleCount n ell p := by
  let e : {d : MarkedDatum n ell // Matches (MarkedPattern d) p} ≃
      ({b : BadDatum n // Matches (BadPattern b) p}⊕
        {C : CanonicalCycleDatum n ell // Matches C.val p}) :=
    { toFun := fun d => match d with
        | ⟨Sum.inl b,hb⟩ => Sum.inl ⟨b,hb⟩
        | ⟨Sum.inr C,hC⟩ => Sum.inr ⟨C,hC⟩
      invFun := fun d => match d with
        | Sum.inl b => ⟨Sum.inl b.val,b.property⟩
        | Sum.inr C => ⟨Sum.inr C.val,C.property⟩
      left_inv := by rintro ⟨d,hd⟩;cases d <;> rfl
      right_inv := by intro d;cases d <;> rfl }
  rw [MarkedMatchingCount,Fintype.card_congr e,Fintype.card_sum]
  simp only [BadCount,CanonicalCycleCount,Nat.card_eq_fintype_card]

theorem actual_mean_marked_count_sum (k ell : ℕ) :
    MeanMarkedCount k ell=MeanBadCount k+MeanCanonicalCycles k ell := by
  unfold MeanMarkedCount MeanBadCount MeanCanonicalCycles
  simp only [actual_marked_matching_count_sum,Nat.cast_add,Finset.sum_add_distrib,add_div]

theorem actual_mean_marked_count_limit (ell : ℕ) [NeZero ell] :
    Tendsto (fun k => MeanMarkedCount k ell) atTop
      (𝓝 (2+(2 : ℝ)^ell/(2*(ell : ℝ)))) := by
  simpa only [actual_mean_marked_count_sum] using
    actual_mean_bad_count_limit.add (actual_mean_canonical_cycles_limit ell)

#print axioms actual_canonical_datum_edge_card
#print axioms actual_bad_datum_edge_card_le_two
#print axioms actual_marked_pattern_injective
#print axioms actual_marked_matching_count_sum
#print axioms actual_mean_marked_count_sum
#print axioms actual_mean_marked_count_limit
end Reference.MD06MixedLowCycleBijections
