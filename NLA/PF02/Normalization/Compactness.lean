module

public import NLA.PF02.Normalization.CompactDefinitions
public import NLA.PF02.Normalization.Continuity
public import NLA.PF02.Normalization.EntryBounds

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Reference.PF02Support
open scoped BigOperators MatrixOrder

theorem psd_set_isClosed (k : ℕ) : IsClosed {H : Mat (Fin k) | H.PosSemidef} := by
  have hs : IsClosed {H : Mat (Fin k) | H.IsHermitian} :=
    isClosed_eq (show Continuous (fun H : Mat (Fin k) => Hᴴ) by fun_prop) continuous_id
  have hw : IsClosed {H : Mat (Fin k) | ∀ x : Fin k → ℝ, 0 ≤ star x ⬝ᵥ H *ᵥ x} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    fun_prop
  convert hs.inter hw using 1
  ext H
  exact Matrix.posSemidef_iff_dotProduct_mulVec

theorem normalized_factor_set_isClosed {p q k : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) :
    IsClosed (normalizedFactorSet (k := k) M) := by
  have hp : IsClosed {H : Mat (Fin k) | H.PosSemidef} := psd_set_isClosed k
  have ha : IsClosed {F : FactorPair p q k | ∀ i, (F.1 i).PosSemidef} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    have hf : Continuous (fun F : FactorPair p q k => F.1 i) := (continuous_apply i).comp continuous_fst
    exact hp.preimage hf
  have hb : IsClosed {F : FactorPair p q k | ∀ j, (F.2 j).PosSemidef} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro j
    have hf : Continuous (fun F : FactorPair p q k => F.2 j) := (continuous_apply j).comp continuous_snd
    exact hp.preimage hf
  have hs : IsClosed {F : FactorPair p q k | rowSum F.1 = 1} :=
    isClosed_eq ((continuous_row_sum p k).comp continuous_fst) continuous_const
  have ht : IsClosed {F : FactorPair p q k | ∀ i j, Matrix.trace (F.1 i * F.2 j) = M i j} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro j
    apply isClosed_eq _ continuous_const
    fun_prop
  exact ha.inter (hb.inter (hs.inter ht))

theorem normalized_factor_set_isCompact {p q k : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) :
    IsCompact (normalizedFactorSet (k := k) M) := by
  let RA : Set (Fin p → Mat (Fin k)) := {A | ∀ i a b, A i a b ∈ Set.Icc (-(k : ℝ)) k}
  let RB : Set (Fin q → Mat (Fin k)) := {B | ∀ j a b, B j a b ∈ Set.Icc (-(∑ i, M i j)) (∑ i, M i j)}
  have hca : IsCompact RA :=
    isCompact_pi_infinite fun i => isCompact_pi_infinite fun a => isCompact_pi_infinite fun b => isCompact_Icc
  have hcb : IsCompact RB :=
    isCompact_pi_infinite fun j => isCompact_pi_infinite fun a => isCompact_pi_infinite fun b => isCompact_Icc
  apply (hca.prod hcb).of_isClosed_subset (normalized_factor_set_isClosed M)
  intro F hF
  rcases hF with ⟨hA, hB, hsum, htrace⟩
  have hpd : (rowSum F.1).PosDef := by rw [hsum]; exact Matrix.PosDef.one
  constructor
  · intro i a b
    have h := normalized_row_entry_bound F.1 hA hpd i a b
    simpa only [normalizedRow, rootSum, hsum, CFC.sqrt_one, inv_one,
      Matrix.one_mul, Matrix.mul_one, Set.mem_Icc, ← abs_le] using h
  · intro j a b
    have h := normalized_column_entry_bound M F.1 F.2 hA hB hpd htrace j a b
    simpa only [normalizedColumn, rootSum, hsum, CFC.sqrt_one,
      Matrix.one_mul, Matrix.mul_one, Set.mem_Icc, ← abs_le] using h

theorem normalized_factor_set_nonempty_of_full_rank {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ j, (B j).PosSemidef)
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j)
    (hrank : M.rank = k * (k + 1) / 2) :
    (normalizedFactorSet (k := k) M).Nonempty := by
  have hs := row_sum_posDef_of_full_trace_rank M A B hA htrace hrank
  refine ⟨(normalizedRow A, normalizedColumn A B), ?_⟩
  exact ⟨normalized_row_posSemidef A hA, normalized_column_posSemidef A B hB,
    normalized_row_sum A hA hs, fun i j => (normalized_trace_pairing A B hs i j).trans (htrace i j)⟩

#print axioms psd_set_isClosed
#print axioms normalized_factor_set_isClosed
#print axioms normalized_factor_set_isCompact
#print axioms normalized_factor_set_nonempty_of_full_rank
end Reference.PF02Normalization
