module

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.
Real adaptation of MI-13 at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
-/
public import NLA.RA08.LiteralJoins.RealSVD.GramBasis

@[expose] public section

set_option autoImplicit false

namespace Reference.RealSVDPackage
noncomputable section

private theorem gram_image_inner {r : ℕ} (A : Square r)
    (v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r)) (hv : GramBasis A v)
    (i j : Fin r) :
    inner ℝ (euclideanLin A (v i)) (euclideanLin A (v j)) =
      singularValue A j.val ^ 2 * inner ℝ (v i) (v j) := by
  calc
    inner ℝ (euclideanLin A (v i)) (euclideanLin A (v j)) =
        inner ℝ (v i) ((euclideanLin A).adjoint (euclideanLin A (v j))) :=
      ((euclideanLin A).adjoint_inner_right (v i) (euclideanLin A (v j))).symm
    _ = singularValue A j.val ^ 2 * inner ℝ (v i) (v j) := by
      rw [hv j, inner_smul_right]

theorem positive_image_orthonormal {r : ℕ} (A : Square r)
    (v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r)) (hv : GramBasis A v) :
    Orthonormal ℝ ((positiveSingularIndices A).domRestrict (normalizedImages A v)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  change inner ℝ (normalizedImages A v i.val) (normalizedImages A v j.val) =
    if i = j then (1 : ℝ) else 0
  simp only [normalizedImages, inner_smul_left, inner_smul_right,
    gram_image_inner A v hv]
  by_cases hij : i = j
  · subst j
    have hi : singularValue A i.val.val ≠ 0 := ne_of_gt i.property
    simp [pow_two, hi]
  · have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    simp only [v.inner_eq_zero hij', mul_zero, if_neg hij]

theorem zero_singular_image {r : ℕ} (A : Square r)
    (v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r)) (hv : GramBasis A v)
    (i : Fin r) (hi : singularValue A i.val = 0) : euclideanLin A (v i) = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  rw [gram_image_inner A v hv i i, hi]
  simp

theorem full_singular_vector_bases {r : ℕ} (A : Square r) :
    ∃ u v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r),
      GramBasis A v ∧ ∀ i, euclideanLin A (v i) = singularValue A i.val • u i := by
  obtain ⟨v, hv⟩ := ordered_gram_basis A
  obtain ⟨u, hu⟩ := positive_image_extension A v (positive_image_orthonormal A v hv)
  refine ⟨u, v, hv, ?_⟩
  intro i
  by_cases hpos : 0 < singularValue A i.val
  · have himem : i ∈ positiveSingularIndices A := hpos
    have hi : singularValue A i.val ≠ 0 := ne_of_gt hpos
    rw [hu i himem, normalizedImages]
    exact (smul_inv_smul₀ hi (euclideanLin A (v i))).symm
  · have hi : singularValue A i.val = 0 :=
      le_antisymm (le_of_not_gt hpos) ((singular_values_semantics A).1 i.val)
    rw [zero_singular_image A v hv i hi, hi]
    simp

#print axioms positive_image_orthonormal
#print axioms zero_singular_image
#print axioms full_singular_vector_bases

end
end Reference.RealSVDPackage


