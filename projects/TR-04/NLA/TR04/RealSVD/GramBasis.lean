module

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.
Real adaptation of MI-13 at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
-/
public import NLA.TR04.RealSVD.SingularSemantics

@[expose] public section

set_option autoImplicit false

namespace Reference.RealSVDPackage
noncomputable section

theorem ordered_gram_basis {r : ℕ} (A : Square r) :
    ∃ v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r), GramBasis A v := by
  let hn := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := r)
  refine ⟨(euclideanLin A).isSymmetric_adjoint_comp_self.eigenvectorBasis hn, ?_⟩
  intro i
  have h := (euclideanLin A).isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn i
  rw [← (euclideanLin A).sq_singularValues_fin hn i] at h
  simpa only [LinearMap.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
    singularValue] using h

theorem positive_image_extension {r : ℕ} (A : Square r)
    (v : OrthonormalBasis (Fin r) ℝ (EuclideanVector r))
    (h : Orthonormal ℝ ((positiveSingularIndices A).domRestrict (normalizedImages A v))) :
    ∃ u : OrthonormalBasis (Fin r) ℝ (EuclideanVector r),
      ∀ i ∈ positiveSingularIndices A, u i = normalizedImages A v i := by
  exact Orthonormal.exists_orthonormalBasis_extension_of_card_eq (by simp) h

#print axioms ordered_gram_basis
#print axioms positive_image_extension

end
end Reference.RealSVDPackage

