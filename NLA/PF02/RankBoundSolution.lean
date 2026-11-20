module

public import NLA.PF02.PaperSymmetricRank

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.PF02.Paper

theorem paper_trace_factor_rank_bound {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin k) (Fin k) ℝ)
    (B : Fin q → Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i, (A i).transpose = A i)
    (h : ∀ i j, Matrix.trace (A i * B j) = M i j) :
    M.rank ≤ k*(k+1)/2 := by
  exact trace_factor_symmetric_rank_le M A B hA h

theorem paper_psd_factor_rank_bound {p q k : ℕ} {M : Mat p q}
    (F : Factorization M k) : M.rank ≤ k*(k+1)/2 := by
  exact factorization_symmetric_rank_le F

end NLA.PF02.Paper
