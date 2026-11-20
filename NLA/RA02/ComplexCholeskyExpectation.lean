module

public import NLA.RA02.ComplexCholeskyProducts
public import NLA.RA02.PaperCholeskyExpectation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper.ComplexHistory

theorem interpolatoryResidual_nonzero {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hk : k < n) (rows cols : Fin k ↪ Fin n) :
    interpolatoryResidual A rows cols ≠ 0 := by
  obtain ⟨p,hp⟩ := exists_unused_label hk rows
  obtain ⟨q,hq⟩ := exists_unused_label hk cols
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k hk.le rows cols))
  have ha := hA (k+1) hk (appendEmbedding rows p hp) (appendEmbedding cols q hq)
  rw [residual_bordered_determinant A rows cols p q hp hq hu] at ha
  intro hzero
  have hz := congrArg (fun M : NLA.RA02.Square n => M p q) hzero
  exact (mul_ne_zero_iff.mp ha).2 hz

theorem cholesky_distinct_prefix_trace {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hpsd : A.PosSemidef)
    (hk : k ≤ n) (h : Fin k ↪ Fin n) :
    ∀ s : Fin (List.ofFn h).length,
      NLA.RA02.realTrace (NLA.RA02.pathResidual A ((List.ofFn h).take s.val)) ≠ 0 := by
  intro s
  have hs : s.val < k := by simpa using s.isLt
  have hsn : s.val < n := lt_of_lt_of_le hs hk
  have hp := NLA.RA02.pathResidual_posSemidef A hpsd ((List.ofFn h).take s.val)
  apply ne_of_gt (NLA.RA02.realTrace_pos hp ?_)
  rw [take_history h hs.le, choleskyPath_distinct A hA hsn.le (historyPrefix h hs.le)]
  exact interpolatoryResidual_nonzero A hA hsn (historyPrefix h hs.le) (historyPrefix h hs.le)

theorem cholesky_terminal_contribution {k : ℕ} (A : NLA.RA02.Square (k+1))
    (hA : AllSquareMinorsNonzero A) (hpsd : A.PosSemidef) (h : Fin k ↪ Fin (k+1)) :
    NLA.RA02.pathContribution A (List.ofFn h) =
      A.det.re / NLA.RA02.prefixTraceProduct A (List.ofFn h) := by
  obtain ⟨p,hp⟩ := exists_unused_label (Nat.lt_succ_self k) h
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k (Nat.le_succ k) h h))
  have he : (NLA.RA02.pathContribution A (List.ofFn h) : ℂ) =
      A.det / (NLA.RA02.prefixTraceProduct A (List.ofFn h) : ℂ) := by
    rw [NLA.RA02.pathContribution, Complex.ofReal_mul,
      cholesky_pathWeight_det A hA hpsd (Nat.le_succ k) h
        (cholesky_distinct_prefix_trace A hA hpsd (Nat.le_succ k) h),
      trace_cast_real _ (NLA.RA02.pathResidual_posSemidef A hpsd _),
      choleskyPath_distinct A hA (Nat.le_succ k) h,
      div_mul_eq_mul_div, terminal_trace_det A h p hp hu]
  simpa only [Complex.ofReal_re, Complex.div_ofReal_re] using congrArg Complex.re he

theorem cholesky_expectation_determinant {k : ℕ} (A : NLA.RA02.Square (k+1))
    (hA : AllSquareMinorsNonzero A) (hpsd : A.PosSemidef) :
    NLA.RA02.expectedTrace A k = A.det.re *
      ∑ h : Fin k ↪ Fin (k+1), (NLA.RA02.prefixTraceProduct A (List.ofFn h))⁻¹ := by
  rw [NLA.RA02.Paper.cholesky_expectation_distinct _ hpsd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  rw [cholesky_terminal_contribution A hA hpsd h, div_eq_mul_inv]

#print axioms cholesky_expectation_determinant
end NLA.RA02.Paper.ComplexHistory
