module

public import NLA.RA02.ComplexPathNormalizers

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper.ComplexHistory

theorem paper_complex_cholesky_history_identity {k : ℕ} (A : NLA.RA02.Square (k+1))
    (hA : AllSquareMinorsNonzero A) (hpsd : A.PosSemidef) :
    NLA.RA02.expectedTrace (A) k = A.det.re *
      ∑ h : Fin k ↪ Fin (k+1), ∏ s : Fin k, 1 / historyTraceNormalizer A h s := by
  exact cholesky_history_identity A hA hpsd

theorem paper_complex_lu_history_identity {k : ℕ} (A : NLA.RA02.Square (k+1))
    (hA : AllSquareMinorsNonzero A) :
    NLA.RA03.expectedError (A) k = Complex.normSq A.det *
      ∑ rows : Fin k ↪ Fin (k+1), ∑ cols : Fin k ↪ Fin (k+1),
        ∏ s : Fin k, 1 / historyFrobeniusNormalizer A rows cols s := by
  exact lu_history_identity A hA

theorem paper_complex_choleskyPath_distinct {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (h : Fin k ↪ Fin n) :
    NLA.RA02.pathResidual A (List.ofFn h) = interpolatoryResidual A h h := by
  exact choleskyPath_distinct A hA hk h

theorem paper_complex_luPath_distinct {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (rows cols : Fin k ↪ Fin n) :
    NLA.RA03.historyResidual A (fun i => some (rows i,cols i)) = interpolatoryResidual A rows cols := by
  exact luPath_distinct A hA hk rows cols

theorem paper_complex_terminal_trace_det {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℂ)
    (rows : Fin k ↪ Fin (k+1)) (p : Fin (k+1)) (hp : p ∉ Set.range rows)
    (hu : IsUnit (A.submatrix rows rows)) :
    (A.submatrix rows rows).det * (interpolatoryResidual A rows rows).trace = A.det := by
  exact terminal_trace_det A rows p hp hu

theorem paper_complex_terminal_frobenius_det {k : ℕ} (A : NLA.RA02.Square (k+1))
    (rows cols : Fin k ↪ Fin (k+1)) (p q : Fin (k+1))
    (hp : p ∉ Set.range rows) (hq : q ∉ Set.range cols)
    (hu : IsUnit (A.submatrix rows cols)) :
    Complex.normSq (A.submatrix rows cols).det *
      NLA.RA03.frobeniusSq (interpolatoryResidual A rows cols) = Complex.normSq A.det := by
  exact terminal_frobenius_det A rows cols p q hp hq hu

theorem paper_complex_determinant_real {n : ℕ} (A : NLA.RA02.Square n) (hA : A.PosSemidef) :
    (A.det.re : ℂ) = A.det := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp hA.det_nonneg).2

theorem paper_complex_residual_semantics {n s : ℕ} (A : NLA.RA02.Square n) (rows cols : Fin s ↪ Fin n) :
    interpolatoryResidual A rows cols = A - A.submatrix id cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id := by
  rfl

theorem paper_complex_trace_semantics {n k : ℕ} (A : NLA.RA02.Square n) (h : Fin k ↪ Fin n) (s : Fin k) :
    historyTraceNormalizer A h s =
      (interpolatoryResidual A (historyPrefix h s.isLt.le) (historyPrefix h s.isLt.le)).trace.re := by
  rfl

theorem paper_complex_frobenius_semantics {n k : ℕ} (A : NLA.RA02.Square n) (rows cols : Fin k ↪ Fin n) (s : Fin k) :
    historyFrobeniusNormalizer A rows cols s = ∑ i, ∑ j,
      Complex.normSq (interpolatoryResidual A (historyPrefix rows s.isLt.le) (historyPrefix cols s.isLt.le) i j) := by
  rfl

theorem paper_complex_determinant_norm_semantics {n : ℕ} (A : NLA.RA02.Square n) :
    Complex.normSq A.det = ‖A.det‖^2 := by
  exact Complex.normSq_eq_norm_sq _

#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_cholesky_history_identity
#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_lu_history_identity
#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_choleskyPath_distinct
#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_luPath_distinct
#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_terminal_trace_det
#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_terminal_frobenius_det
#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_determinant_real
#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_residual_semantics
#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_trace_semantics
#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_frobenius_semantics
#print axioms NLA.RA02.Paper.ComplexHistory.paper_complex_determinant_norm_semantics
end NLA.RA02.Paper.ComplexHistory
