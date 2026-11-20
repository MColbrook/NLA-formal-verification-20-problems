module

/- Complex-field adaptation of Paper/Degenerate.lean, with Codex assistance. -/
public import NLA.RA09.ComplexRank

@[expose] public section

/-! The zero-tail and full-rank cases use no division by the cutoff. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder
namespace NLA.RA09.ComplexPaper

open scoped Matrix.Norms.Frobenius in
theorem frobeniusSquared_eq_zero {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) :
    frobeniusSquared M = 0 ↔ M = 0 := by
  rw [frobeniusSquared_norm, sq_eq_zero_iff]
  exact norm_eq_zero

theorem spectral_tail_zero_of_cutoff_zero {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) (hk : k < n)
    (hzero : d.eigenvalues ⟨k,hk⟩ = 0) : spectralTail d k = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hki : (⟨k,hk⟩ : Fin n) ≤ i := (Finset.mem_filter.mp hi).2
  have heig : d.eigenvalues i = 0 := le_antisymm
    (hzero ▸ d.decreasing hki) (d.nonnegative i)
  simp only [heig, zero_pow (by decide : 2 ≠ 0)]

theorem spectral_tail_full {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) : spectralTail d n = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  exact False.elim ((Nat.not_le_of_lt i.isLt) (Finset.mem_filter.mp hi).2)

theorem zero_tail_residual_exact {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (k : ℕ) (hk : k ≤ n) (hB : B.rank ≤ k)
    (hzero : spectralTail dA k = 0) (η : ℝ)
    (herror : frobeniusSquared (A-B) ≤ (1+η)*spectralTail dA k) :
    A = B ∧ frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) =
      functionTail dA f k := by
  have hAB : A = B := by
    apply sub_eq_zero.mp
    apply (frobeniusSquared_eq_zero _).mp
    apply le_antisymm ?_ (frobeniusSquared_nonneg _)
    simpa only [hzero, mul_zero] using herror
  refine ⟨hAB, ?_⟩
  have htail : functionTail dB f k = functionTail dA f k := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : k ≤ i.val := (Finset.mem_filter.mp hi).2
    rw [eigenvalue_zero_of_rank_le dB k hB i hik,
      eigenvalue_zero_of_rank_le dA k (by simpa only [hAB] using hB) i hik]
  calc
    _ = frobeniusSquared (functionalCalculus f B - functionTruncation dB f k) := by rw [hAB]
    _ = functionTail dB f k := (truncation_semantics_proved dB k hk f).2.2.2.1
    _ = _ := htail

#print axioms spectral_tail_zero_of_cutoff_zero
#print axioms spectral_tail_full
#print axioms zero_tail_residual_exact

end NLA.RA09.ComplexPaper
