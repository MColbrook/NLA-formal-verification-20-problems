module

public import NLA.MD06.BadJointMoments.Definitions
public import NLA.MD06.BadPatternCounts.FirstMoment
public import NLA.MD06.SimplicityBonferroni.Average

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadJointMoments
open Reference.MD06Simplicity Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06FiniteProbability Reference.MD06BadPatternCounts
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_joint_matching_iff {n q : ℕ} (f : JointDatum n q) (p : Pairing n) :
    Matches (JointPattern f) p ↔ ∀ i : Fin q, Matches (BadPattern (f i)) p := by
  constructor
  · intro h i e he
    exact h e (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,he⟩)
  · intro h e he
    rcases Finset.mem_biUnion.mp he with ⟨i,hi,he⟩
    exact h i e he

theorem actual_joint_count_desc_factorial {n q : ℕ} (p : Pairing n) :
    JointCount (q := q) p = (BadCount p).descFactorial q := by
  let e : {f : JointDatum n q // Matches (JointPattern f) p} ≃
      (Fin q ↪ {z : BadDatum n // Matches (BadPattern z) p}) :=
    { toFun := fun f =>
        { toFun := fun i => ⟨f.val i,(actual_joint_matching_iff f.val p).mp f.property i⟩
          inj' := fun i j h => f.val.injective (congrArg Subtype.val h) }
      invFun := fun f => ⟨
        { toFun := fun i => (f i).val
          inj' := fun i j h => f.injective (Subtype.ext h) },
        (actual_joint_matching_iff _ p).mpr (fun i => (f i).property)⟩
      left_inv := by
        intro f
        apply Subtype.ext
        apply Function.Embedding.ext
        intro i
        rfl
      right_inv := by
        intro f
        apply Function.Embedding.ext
        intro i
        rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_embedding_eq,Fintype.card_fin] at h
  simpa only [JointCount,FamilyMatchingCount,BadCount,← Nat.card_eq_fintype_card] using h

theorem actual_bad_descending_sum_joint {n q : ℕ} :
    (∑ p : Pairing n, (BadCount p).descFactorial q) =
      ∑ f : JointDatum n q, PatternCount (JointPattern f) := by
  have h := actual_family_matching_sum (JointPattern (n := n) (q := q))
  change (∑ p : Pairing n, JointCount (q := q) p) = _ at h
  simpa only [actual_joint_count_desc_factorial] using h

theorem actual_mean_bad_descending_joint_sum (k q : ℕ) :
    MeanBadDescending k q =
      (∑ f : JointDatum (Size k) q, (PatternCount (JointPattern f) : ℝ)) /
        (Fintype.card (Pairing (Size k)) : ℝ) := by
  simpa only [MeanBadDescending,Nat.cast_sum] using
    congrArg (fun x : ℕ => (x : ℝ)/(Fintype.card (Pairing (Size k)) : ℝ))
      (actual_bad_descending_sum_joint (n := Size k) (q := q))

theorem actual_mean_bad_descending_choose (k q : ℕ) :
    MeanBadDescending k q = (q.factorial : ℝ)*MeanBadChoose k q := by
  unfold MeanBadDescending MeanBadChoose
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  rw [← Finset.mul_sum]
  ring

theorem actual_mean_bad_choose_descending (k q : ℕ) :
    MeanBadChoose k q = MeanBadDescending k q/(q.factorial : ℝ) := by
  rw [actual_mean_bad_descending_choose]
  have hq : (q.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero q
  field_simp [hq]

theorem actual_mean_bad_descending_zero (k : ℕ) :
    MeanBadDescending k 0 = 1 := by
  unfold MeanBadDescending
  simp only [Nat.descFactorial_zero,Nat.cast_one,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

theorem actual_mean_bad_descending_one (k : ℕ) :
    MeanBadDescending k 1 = MeanBadCount k := by
  simp only [MeanBadDescending,MeanBadCount,Nat.descFactorial_one]

theorem actual_mean_bad_descending_one_limit :
    Tendsto (fun k : ℕ => MeanBadDescending k 1) atTop (𝓝 (2 : ℝ)) := by
  simpa only [actual_mean_bad_descending_one] using actual_mean_bad_count_limit

theorem actual_simple_probability_bonferroni_joint (k : ℕ) :
    (∑ q ∈ Finset.range 8, (-1 : ℝ)^q *
      (MeanBadDescending k q/(q.factorial : ℝ))) ≤
        ((UniformPairing k).toOuterMeasure {p | IsSimplePairing p}).toReal := by
  have h := actual_simple_probability_bonferroni_seven k
  change (∑ q ∈ Finset.range 8, (-1 : ℝ)^q * MeanBadChoose k q) ≤ _ at h
  simpa only [actual_mean_bad_choose_descending] using h

#print axioms actual_joint_matching_iff
#print axioms actual_joint_count_desc_factorial
#print axioms actual_bad_descending_sum_joint
#print axioms actual_mean_bad_descending_joint_sum
#print axioms actual_mean_bad_descending_choose
#print axioms actual_mean_bad_choose_descending
#print axioms actual_mean_bad_descending_zero
#print axioms actual_mean_bad_descending_one
#print axioms actual_mean_bad_descending_one_limit
#print axioms actual_simple_probability_bonferroni_joint
end Reference.MD06BadJointMoments
