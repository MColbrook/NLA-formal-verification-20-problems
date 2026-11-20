module

public import NLA.PF02.Normalization.Normalization

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Reference.PF02Support
open scoped BigOperators MatrixOrder

theorem psd_family_each_le_sum {p k : ℕ} (A : Fin p → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) (i : Fin p) : A i ≤ rowSum A :=
  Finset.single_le_sum (f := A) (fun j _ => (hA j).nonneg) (Finset.mem_univ i)

theorem normalized_row_le_one {p k : ℕ} (A : Fin p → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) (hsum : (rowSum A).PosDef) (i : Fin p) :
    normalizedRow A i ≤ 1 := by
  have h := psd_family_each_le_sum (normalizedRow A) (normalized_row_posSemidef A hA) i
  simpa only [rowSum, normalized_row_sum A hA hsum] using h

#print axioms psd_family_each_le_sum
#print axioms normalized_row_le_one
end Reference.PF02Normalization
