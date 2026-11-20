module

public import NLA.RA02.PaperInterpolationDefinitions
public import NLA.RA02.PaperPrefixInverse

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem interpolation_equation {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (t : ℝ) (hu : IsUnit (prefixMatrix hs.le rows t)) :
    prefixMatrix hs.le rows t *ᵥ interpolationCoefficients hs rows t =
      (fun i => nextColumn hs t (rows i)) := by
  rw [interpolationCoefficients, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mulVec]

theorem interpolation_vanishes_on_rows {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (t : ℝ) (hu : IsUnit (prefixMatrix hs.le rows t)) (i : Fin s) :
    interpolationResidual hs rows t (rows i) = 0 := by
  have he := congrFun (interpolation_equation hs rows t hu) i
  simp only [prefixMatrix, Matrix.mulVec, dotProduct, Matrix.submatrix_apply] at he
  simp only [interpolationResidual, Pi.sub_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq]
  rw [he, sub_self]

def missingNextColumnVector {n s : ℕ} (rows : Fin s ↪ Fin n) : Fin s → ℝ :=
  fun i => if s < (rows i).val then ((rows i).val+s+2 : ℝ)⁻¹ else 0

theorem missing_next_column {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (hm : (⟨s,hs⟩ : Fin n) ∉ Set.range rows) (t : ℝ) :
    (fun i => nextColumn hs t (rows i)) = t^(s+1) • missingNextColumnVector rows := by
  funext i
  have hi : rows i ≠ ⟨s,hs⟩ := by intro h; exact hm ⟨i,h⟩
  simp only [nextColumn, lower, if_neg hi, missingNextColumnVector, Pi.smul_apply, smul_eq_mul]
  change (if s < (rows i).val then t^(s+1) / ((rows i).val+s+2 : ℕ) else 0) = _
  split_ifs <;> simp [div_eq_mul_inv]

theorem missing_next_coefficients {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (hm : (⟨s,hs⟩ : Fin n) ∉ Set.range rows) {t : ℝ} (ht : t ≠ 0) :
    interpolationCoefficients hs rows t =
      t • (scaledPrefixInverse hs.le rows t *ᵥ missingNextColumnVector rows) := by
  rw [interpolationCoefficients, missing_next_column hs rows hm, scaledPrefixInverse_eq hs.le rows ht,
    Matrix.mulVec_smul, Matrix.smul_mulVec, smul_smul, pow_succ, mul_comm t]

#print axioms missing_next_coefficients
end NLA.RA02.Paper
