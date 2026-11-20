module

public import NLA.PF02.Normalization.Normalization

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Reference.PF02Support
open scoped BigOperators MatrixOrder

theorem psd_entry_abs_le_trace {k : ℕ} (H : Mat (Fin k)) (hH : H.PosSemidef)
    (i j : Fin k) : |H i j| ≤ Matrix.trace H := by
  have hp := hH.dotProduct_mulVec_nonneg (Pi.single i 1 + Pi.single j 1)
  have hm := hH.dotProduct_mulVec_nonneg (Pi.single i 1 - Pi.single j 1)
  simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct,
    sub_dotProduct, dotProduct_add, dotProduct_sub, single_dotProduct,
    Matrix.mulVec_single_one, Matrix.col_apply, one_mul] at hp hm
  have hij : H j i = H i j := by simpa only [star_trivial] using hH.isHermitian.apply i j
  have hi : H i i ≤ Matrix.trace H := by
    simpa [Matrix.trace, Matrix.diag] using (Finset.single_le_sum (f := fun a => H a a)
      (fun a ha => hH.diag_nonneg (i := a)) (Finset.mem_univ i))
  have hj : H j j ≤ Matrix.trace H := by
    simpa [Matrix.trace, Matrix.diag] using (Finset.single_le_sum (f := fun a => H a a)
      (fun a ha => hH.diag_nonneg (i := a)) (Finset.mem_univ j))
  rw [hij] at hp hm
  apply abs_le.mpr
  constructor <;> linarith

theorem normalized_row_entry_bound {p k : ℕ} (A : Fin p → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) (hsum : (rowSum A).PosDef)
    (i : Fin p) (a b : Fin k) : |normalizedRow A i a b| ≤ k := by
  have ht : (∑ i, Matrix.trace (normalizedRow A i)) = k := by
    rw [← Matrix.trace_sum, normalized_row_sum A hA hsum]
    simp
  have hle : Matrix.trace (normalizedRow A i) ≤ k := by
    rw [← ht]
    exact Finset.single_le_sum (fun j hj => (normalized_row_posSemidef A hA j).trace_nonneg)
      (Finset.mem_univ i)
  exact (psd_entry_abs_le_trace _ (normalized_row_posSemidef A hA i) a b).trans hle

theorem normalized_column_entry_bound {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ j, (B j).PosSemidef)
    (hsum : (rowSum A).PosDef)
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j)
    (j : Fin q) (a b : Fin k) : |normalizedColumn A B j a b| ≤ ∑ i, M i j := by
  rw [← normalized_column_trace M A B hA hsum htrace j]
  exact psd_entry_abs_le_trace _ (normalized_column_posSemidef A B hB j) a b

#print axioms psd_entry_abs_le_trace
#print axioms normalized_row_entry_bound
#print axioms normalized_column_entry_bound
end Reference.PF02Normalization
