module

public import NLA.PF02.UniformPositiveOrientation.NormalizedTopology
public import NLA.PF02.UniformPositiveOrientation.PerturbationFactors

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization Set Filter
open scoped Topology BigOperators MatrixOrder

theorem shifted_row_sum_posDef {p k : ℕ} (A : Fin p → Matrix (Fin k) (Fin k) ℝ)
    (hA : (rowSum A).PosDef) (η : ℝ) (hη : 0 ≤ η) :
    (rowSum (shiftedFactors A η)).PosDef := by
  have he : rowSum (shiftedFactors A η) = rowSum A + ∑ _i : Fin p, η • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    simp only [rowSum,shiftedFactors,Finset.sum_add_distrib]
  rw [he]
  exact hA.add_posSemidef (Matrix.posSemidef_sum _ (fun _ _ => Matrix.PosDef.one.posSemidef.smul hη))

theorem continuousOn_shifted_normalization {p k : ℕ}
    (A : Fin p → Matrix (Fin k) (Fin k) ℝ) (hA : (rowSum A).PosDef) :
    ContinuousOn (fun η : ℝ => normalizedRow (shiftedFactors A η)) (Ici 0) := by
  apply continuousOn_pi.mpr
  intro i
  apply (continuousOn_normalized_row p k i).comp (show Continuous (shiftedFactors A) by
    unfold shiftedFactors; fun_prop).continuousOn
  exact fun η hη => shifted_row_sum_posDef A hA η hη

theorem actual_zero_normalization_orientation_product_pos {r : ℕ}
    (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r)) :
    0 < orientationPolynomial (leadingRows (r := r) F.val.1) *
      orientationPolynomial (leadingRows (r := r) (normalizedRow F.val.1)) := by
  have hPD : (rowSum F.val.1).PosDef :=
    actual_factor_row_sum_posDef (enumeratedRealGram r) (enumerated_real_gram_rank r) F
  have hu := (Matrix.isUnit_iff_isUnit_det (rootSum F.val.1)).mp (root_sum_isUnit F.val.1 hPD)
  have hi : ((rootSum F.val.1)⁻¹).det ≠ 0 := ((rootSum F.val.1).isUnit_nonsing_inv_det hu).ne_zero
  have ht : ((rootSum F.val.1)⁻¹).transpose = (rootSum F.val.1)⁻¹ := by
    ext i j
    simpa only [Matrix.transpose_apply,star_trivial] using
      (root_sum_posSemidef F.val.1).inv.isHermitian.apply i j
  have he : leadingRows (r := r) (normalizedRow F.val.1) =
      fun p => ((rootSum F.val.1)⁻¹).transpose * leadingRows (r := r) F.val.1 p * (rootSum F.val.1)⁻¹ := by
    funext p
    simp only [leadingRows,Reference.PF02BlockSupportRecovery.blockRows,normalizedRow,ht]
  rw [he]
  exact actual_invertible_orientation_product_pos F ((rootSum F.val.1)⁻¹) hi

theorem actual_zero_normalized_witness_product_negative (r : ℕ) :
    orientationPolynomial (leadingRows (r := r) (normalizedRow (enumeratedFactor r))) *
      orientationPolynomial (leadingRows (r := r) (normalizedRow (enumeratedReflectedFactor r))) < 0 := by
  let F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r) :=
    ⟨(enumeratedFactor r,enumeratedFactor r),enumerated_factorization r⟩
  let G : NLA.PF02.Factorization (enumeratedRealGram r) (3+r) :=
    ⟨(enumeratedReflectedFactor r,enumeratedReflectedFactor r),enumerated_reflected_factorization r⟩
  have hf := actual_zero_normalization_orientation_product_pos F
  have hg := actual_zero_normalization_orientation_product_pos G
  have hn := actual_witness_orientation_product_negative r
  change 0 < orientationPolynomial (leadingRows (r := r) (enumeratedFactor r)) *
    orientationPolynomial (leadingRows (r := r) (normalizedRow (enumeratedFactor r))) at hf
  change 0 < orientationPolynomial (leadingRows (r := r) (enumeratedReflectedFactor r)) *
    orientationPolynomial (leadingRows (r := r) (normalizedRow (enumeratedReflectedFactor r))) at hg
  rcases mul_neg_iff.mp hn with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hfa := (mul_pos_iff.mp hf).resolve_right (fun h => (not_lt_of_gt ha) h.1)
    have hgb := (mul_pos_iff.mp hg).resolve_left (fun h => (not_lt_of_gt hb) h.1)
    exact mul_neg_of_pos_of_neg hfa.2 hgb.2
  · have hfa := (mul_pos_iff.mp hf).resolve_left (fun h => (not_lt_of_gt ha) h.1)
    have hgb := (mul_pos_iff.mp hg).resolve_right (fun h => (not_lt_of_gt hb) h.1)
    exact mul_neg_of_neg_of_pos hfa.2 hgb.2

#print axioms shifted_row_sum_posDef
#print axioms continuousOn_shifted_normalization
#print axioms actual_zero_normalization_orientation_product_pos
#print axioms actual_zero_normalized_witness_product_negative
end Reference.PF02UniformPositiveOrientation
