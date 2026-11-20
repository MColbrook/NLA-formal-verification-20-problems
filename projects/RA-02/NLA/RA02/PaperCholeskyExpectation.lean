module

public import NLA.RA02.PaperHistoryTrace
public import NLA.RA02.PaperCholeskyZeroHistories

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper

theorem cholesky_expectation_distinct {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) :
    NLA.RA02.expectedTrace A k =
      ∑ h : Fin k ↪ Fin n, NLA.RA02.pathContribution A (List.ofFn h) := by
  unfold NLA.RA02.expectedTrace
  symm
  apply Fintype.sum_of_injective (fun h : Fin k ↪ Fin n => (h : Fin k → Fin n))
    (fun a b hab => Function.Embedding.ext (fun i => congrFun hab i))
  · intro f hf
    apply cholesky_repeated_contribution A hA
    intro hn
    exact hf ⟨⟨f, List.nodup_ofFn.mp hn⟩, rfl⟩
  · intro h
    rfl

theorem cholesky_expectation_determinant {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hA : AllSquareMinorsNonzero A) (hpsd : (complexify A).PosSemidef) :
    NLA.RA02.expectedTrace (complexify A) k = A.det *
      ∑ h : Fin k ↪ Fin (k+1), (NLA.RA02.prefixTraceProduct (complexify A) (List.ofFn h))⁻¹ := by
  rw [cholesky_expectation_distinct _ hpsd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [cholesky_terminal_contribution_psd A hA hpsd h, div_eq_mul_inv]

#print axioms cholesky_expectation_determinant
end NLA.RA02.Paper
