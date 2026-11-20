module

public import NLA.PF02.BlockSupportRecovery.FiniteRank
public import NLA.PF02.BlockConstruction.MinimalRank
public import NLA.PF02.SupportBridge.Supports
public import NLA.PF02.IntrinsicSupport.DimensionSupport

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockSupportRecovery
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction Reference.PF02Support
open Reference.PF02PositiveBasis Reference.PF02IntrinsicSupport
open scoped BigOperators MatrixOrder

theorem actual_block_trace {r : ℕ} (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r))
    (p q : BlockIndex r) : trace (blockRows F.val.1 p * blockRows F.val.2 q) = blockGram r p q := by
  have h := F.property.2.2 (Fintype.equivFin (BlockIndex r) p) (Fintype.equivFin (BlockIndex r) q)
  simpa [blockRows, enumerated_real_gram_eq, finite_block_gram_eq] using h

theorem actual_trailing_sum_posSemidef {r : ℕ}
    (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r)) : (trailingSum F.val.2).PosSemidef :=
  psd_sum (fun p : SymIndex r => blockRows F.val.2 (Sum.inr (Sum.inl p)))
    (fun _p => F.property.2.1 _)

theorem actual_block_supported {r : ℕ}
    (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r)) :
    (∀ p : SymIndex r, SupportedOn (blockRows F.val.2 (Sum.inr (Sum.inl p))) (image (trailingSum F.val.2))) ∧
    (∀ p : SymIndex 3, SupportedOn (blockRows F.val.1 (Sum.inl p)) (kernel (trailingSum F.val.2))) := by
  constructor
  · intro p
    exact psd_family_each_supported_sum_image
      (fun q : SymIndex r => blockRows F.val.2 (Sum.inr (Sum.inl q))) (fun q => F.property.2.1 _) p
  · intro p
    apply psd_trace_zero_family_supported_common_kernel
      (blockRows F.val.1 (Sum.inl p)) (fun q : SymIndex r => blockRows F.val.2 (Sum.inr (Sum.inl q)))
      (F.property.1 _) (fun q => F.property.2.1 _)
    intro q
    rw [actual_block_trace, block_gram_zero_cross]

theorem actual_recovered_support_dimensions {r : ℕ}
    (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r)) :
    (trailingSum F.val.2).rank = r ∧
    Module.finrank ℝ (image (trailingSum F.val.2)) = r ∧
    Module.finrank ℝ (kernel (trailingSum F.val.2)) = 3 := by
  let Q := trailingSum F.val.2
  have hs := actual_block_supported F
  have hlead := finite_psd_supported_trace_rank_le (positiveGram 3)
    (fun p : SymIndex 3 => blockRows F.val.1 (Sum.inl p))
    (fun p : SymIndex 3 => blockRows F.val.2 (Sum.inl p)) (kernel Q)
    (fun p => F.property.1 _) hs.2 (by intro p q; rw [actual_block_trace, block_gram_leading])
  have htail := finite_psd_supported_trace_rank_le (positiveGram r).transpose
    (fun p : SymIndex r => blockRows F.val.2 (Sum.inr (Sum.inl p)))
    (fun p : SymIndex r => blockRows F.val.1 (Sum.inr (Sum.inl p))) (image Q)
    (fun _p => F.property.2.1 _) hs.1 (by
      intro p q
      rw [Matrix.trace_mul_comm, actual_block_trace, block_gram_trailing]
      rfl)
  rw [positive_gram_rank] at hlead
  rw [Matrix.rank_transpose, positive_gram_rank] at htail
  have hk : 3 ≤ Module.finrank ℝ (kernel Q) := triangular_rank_dimension_le hlead
  have hi : r ≤ Module.finrank ℝ (image Q) := triangular_rank_dimension_le htail
  have hsum := image_kernel_finrank_sum Q
  have heI : Module.finrank ℝ (image Q) = r := by omega
  have heK : Module.finrank ℝ (kernel Q) = 3 := by omega
  exact ⟨(rank_eq_image_finrank Q).trans heI, heI, heK⟩

#print axioms actual_block_trace
#print axioms actual_trailing_sum_posSemidef
#print axioms actual_block_supported
#print axioms actual_recovered_support_dimensions
end Reference.PF02BlockSupportRecovery
