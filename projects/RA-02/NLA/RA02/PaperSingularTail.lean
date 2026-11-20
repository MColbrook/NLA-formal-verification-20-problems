module

public import NLA.RA02.PaperRankTailLimit

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology ComplexOrder Matrix.Norms.L2Operator
open Filter
namespace NLA.RA02.Paper

theorem symmetric_eigenvalues_congr {n m : ℕ}
    {S T : Module.End ℂ (EuclideanSpace ℂ (Fin n))} (he : S = T)
    (hS : S.IsSymmetric) (hT : T.IsSymmetric)
    (hm : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = m) (i : Fin m) :
    hS.eigenvalues hm i = hT.eigenvalues hm i := by
  subst T
  rfl

theorem gram_operator {n : ℕ} (A : NLA.RA02.Square n) :
    (Matrix.toEuclideanLin A).adjoint ∘ₗ Matrix.toEuclideanLin A =
      Matrix.toEuclideanLin (A.conjTranspose * A) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change Matrix.toLpLin 2 2 A.conjTranspose ∘ₗ Matrix.toLpLin 2 2 A = _
  rw [← Matrix.toLpLin_mul_same]

theorem singular_squared_gram_eigenvalue {n : ℕ} (A : NLA.RA02.Square n) (i : Fin n) :
    NLA.RA03.singularValue A i.val ^ 2 =
      NLA.RA02.orderedEigenvalues (A.conjTranspose*A)
        (Matrix.isHermitian_conjTranspose_mul_self A) i := by
  let j : Fin (Fintype.card (Fin n)) := Fin.cast (Fintype.card_fin n).symm i
  have hh := (Matrix.toEuclideanLin A).sq_singularValues_fin finrank_euclideanSpace j
  have he := symmetric_eigenvalues_congr (gram_operator A)
    (Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_conjTranspose_mul_self A))
    finrank_euclideanSpace j
  have hh' := hh.trans he
  simpa [NLA.RA03.singularValue, NLA.RA02.orderedEigenvalues,
    Matrix.IsHermitian.eigenvalues₀, j] using hh'

theorem inverse_gram_norm {n : ℕ} (A : NLA.RA02.Square n) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (A.conjTranspose*A)⁻¹‖ =
      ‖Matrix.toEuclideanCLM (𝕜:=ℂ) A⁻¹‖^2 := by
  change ‖(A.conjTranspose*A)⁻¹‖ = ‖A⁻¹‖^2
  rw [Matrix.mul_inv_rev, ← Matrix.conjTranspose_nonsing_inv]
  simpa only [Matrix.star_eq_conjTranspose, pow_two] using CStarRing.norm_self_mul_star (x:=A⁻¹)

theorem singular_last_sq_eq_eigenvalue_sq (r : ℕ) (A : NLA.RA02.Square (r+1)) (hA : A.PosDef) :
    NLA.RA03.singularValue A r ^ 2 =
      NLA.RA02.orderedEigenvalues A hA.isHermitian (Fin.last r)^2 := by
  have hG := Matrix.PosDef.conjTranspose_mul_self A (Matrix.mulVec_injective_iff_isUnit.mpr hA.isUnit)
  have hn := inverse_norm_last_eigenvalue r (A.conjTranspose*A) hG
  rw [inverse_gram_norm, inverse_norm_last_eigenvalue r A hA,
    ← singular_squared_gram_eigenvalue A (Fin.last r)] at hn
  apply inv_injective
  simpa only [inv_pow, Fin.val_last] using hn.symm

theorem singularTailSq_last (r : ℕ) (A : NLA.RA02.Square (r+1)) :
    NLA.RA03.singularTailSq A r = NLA.RA03.singularValue A r^2 := by
  simp [NLA.RA03.singularTailSq]

theorem familySingularTailSquared_eq (r : ℕ) {t : ℝ} (ht : 0 < t) :
    familySingularTailSquared r t = (familyRankTail r t)^2 := by
  rw [familySingularTailSquared, singularTailSq_last,
    singular_last_sq_eq_eigenvalue_sq r _ (complexify_posDef _ (sharpFamily_posDef _ _ ht)),
    familyRankTail_eq_last r ht]

theorem familySingularTailSquared_epsilon_limit (r : ℕ) :
    Tendsto (fun t : ℝ => familySingularTailSquared r t / epsilon (r+1) t^(2*r))
      (𝓝[>] 0) (𝓝 1) := by
  have hh := (familyRankTail_epsilon_limit r).pow 2
  simp only [one_pow] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [familySingularTailSquared_eq r ht, div_pow, ← pow_mul, Nat.mul_comm r 2]

theorem sharp_lu_singularTail_limit (r : ℕ) :
    Tendsto (fun t : ℝ => NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r /
      familySingularTailSquared r t) (𝓝[>] 0) (𝓝 ((4 : ℝ)^r)) := by
  have hh := (sharp_lu_epsilon_limit r).div (familySingularTailSquared_epsilon_limit r) one_ne_zero
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have he : epsilon (r+1) t ≠ 0 := pow_ne_zero _ (ne_of_gt (show 0 < t from ht))
  change (NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r / epsilon (r+1) t^(2*r)) /
    (familySingularTailSquared r t / epsilon (r+1) t^(2*r)) = _
  rw [div_div_div_cancel_right₀ (pow_ne_zero (2*r) he)]

#print axioms sharp_lu_singularTail_limit
end NLA.RA02.Paper
