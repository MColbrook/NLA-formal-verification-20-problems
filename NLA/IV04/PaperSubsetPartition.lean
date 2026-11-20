module

public import NLA.IV04.PaperSubsetPartitionDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction

private theorem selected_signed_total {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (selected : ι → Bool) :
    signedTotal w (fun i => if selected i then 1 else -1) =
      2 * ((∑ i, if selected i then w i else 0 : ℕ) : ℤ) - ((∑ i, w i : ℕ) : ℤ) := by
  simp only [signedTotal, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  calc
    (∑ i, (if selected i then 1 else -1) * (w i : ℤ)) =
        ∑ i, (2 * (if selected i then (w i : ℤ) else 0) - (w i : ℤ)) := by
      apply Finset.sum_congr rfl
      intro i _
      cases selected i <;> simp <;> ring
    _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem subset_sum_iff_signed_target {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (t : ℕ) :
    HasSubsetSum w t ↔ ∃ s, IsSigned s ∧
      signedTotal w s = 2*(t : ℤ) - ((∑ i, w i : ℕ) : ℤ) := by
  constructor
  · rintro ⟨selected, h⟩
    refine ⟨(fun i => if selected i then 1 else -1), ?_, ?_⟩
    · intro i; cases selected i <;> simp <;> ring
    · rw [selected_signed_total, h]
  · rintro ⟨s, hs, ht⟩
    let selected : ι → Bool := fun i => decide (s i = 1)
    have heq : s = fun i => if selected i then 1 else -1 := by
      funext i
      rcases hs i with h | h <;> simp [selected, h]
    refine ⟨selected, ?_⟩
    rw [heq, selected_signed_total] at ht
    have hcast : ((∑ i, if selected i then w i else 0 : ℕ) : ℤ) = (t : ℤ) := by
      omega
    exact_mod_cast hcast

theorem signed_total_abs_le {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (s : ι → ℤ) (hs : IsSigned s) :
    |signedTotal w s| ≤ ((∑ i, w i : ℕ) : ℤ) := by
  unfold signedTotal
  calc
    |∑ i, s i * (w i : ℤ)| ≤ ∑ i, |s i * (w i : ℤ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ((∑ i, w i : ℕ) : ℤ) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      rcases hs i with h | h <;> simp [h]

private theorem padded_signed_total {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (t : ℕ) (s : ι ⊕ Bool → ℤ) :
    signedTotal (subsetPartitionWeights w t) s =
      signedTotal w (fun i => s (Sum.inl i)) +
      s (Sum.inr false) * (((∑ i, w i : ℕ) : ℤ) + 2*(t : ℤ) + 1) +
      s (Sum.inr true) * (2*((∑ i, w i : ℕ) : ℤ) + 1) := by
  simp [signedTotal, subsetPartitionWeights, Fintype.sum_sum_type, add_assoc, add_comm, add_left_comm]

/-- A literal positive two-weight padding converts subset sum to signed PARTITION. -/
theorem subset_partition_iff {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (t : ℕ) :
    SignedPartition (subsetPartitionWeights w t) ↔ HasSubsetSum w t := by
  rw [subset_sum_iff_signed_target]
  constructor
  · rintro ⟨s, hs, hz⟩
    let q : ι → ℤ := fun i => s (Sum.inl i)
    have hq : IsSigned q := fun i => hs (Sum.inl i)
    have hab := abs_le.mp (signed_total_abs_le w q hq)
    rw [padded_signed_total] at hz
    change signedTotal w q + _ + _ = 0 at hz
    rcases hs (Sum.inr false) with ha | ha <;>
      rcases hs (Sum.inr true) with hb | hb
    · rw [ha, hb] at hz
      nlinarith
    · rw [ha, hb] at hz
      exact ⟨q, hq, by linarith⟩
    · rw [ha, hb] at hz
      refine ⟨(fun i => -q i), ?_, ?_⟩
      · intro i; rcases hq i with h | h <;> simp [h]
      · have hneg : signedTotal w (fun i => -q i) = -signedTotal w q := by
          simp [signedTotal, ← Finset.sum_neg_distrib, neg_mul]
        rw [hneg]
        linarith
    · rw [ha, hb] at hz
      nlinarith
  · rintro ⟨q, hq, ht⟩
    let s : ι ⊕ Bool → ℤ := Sum.elim q (fun b => if b then 1 else -1)
    refine ⟨s, ?_, ?_⟩
    · intro i
      cases i with
      | inl j => exact hq j
      | inr b => cases b <;> simp [s]
    · rw [padded_signed_total]
      change signedTotal w q + (-1) * _ + 1 * _ = 0
      rw [ht]
      ring

theorem subset_partition_weights_positive {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (t : ℕ) (hw : ∀ i, 0 < w i) :
    ∀ i, 0 < subsetPartitionWeights w t i := by
  intro i
  cases i with
  | inl j => exact hw j
  | inr b => cases b <;> simp [subsetPartitionWeights]

theorem paper_partition_exact_signed (P : IV04.Paper.IntegerPartition) :
    P.HasPartition ↔ SignedPartition P.weight := Iff.rfl

#print axioms subset_sum_iff_signed_target
#print axioms signed_total_abs_le
#print axioms subset_partition_iff
#print axioms subset_partition_weights_positive
#print axioms paper_partition_exact_signed
end IV04.Paper.Computational.SATReduction