module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual real Gram basis and transpose singular-value identities, extending the
checked MI-13/RA02 adaptations; upstream commit e375a6fc0a12df52c4f5a38b53df78b837e1c390.
New reference-only equality infrastructure by Codex, 2026-10-03. -/
public import NLA.TR04.OptimalityEquality.Definitions
public import NLA.TR04.RealSVD.Compression

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage Reference.RealColumnCompression
open scoped BigOperators Matrix

theorem leftBasis_gram {m n : ℕ} (A : Rect m n) :
    RectangularGramBasis A.transpose (leftBasis A) := by
  intro i
  let hn := finrank_euclideanSpace_fin (𝕜 := ℝ) (n := m)
  have h := (euclideanLin A.transpose).isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn i
  rw [← (euclideanLin A.transpose).sq_singularValues_fin hn i] at h
  simpa only [leftBasis, LinearMap.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
    singularValue] using h

theorem leftVectorMatrix_orthogonal {m n : ℕ} (A : Rect m n) :
    IsOrthogonal (leftVectorMatrix A) := basisMatrix_orthogonal (leftBasis A)

theorem leftVectorMatrix_gram_diagonal {m n : ℕ} (A : Rect m n) :
    (leftVectorMatrix A).transpose * (A * A.transpose) * leftVectorMatrix A =
      Matrix.diagonal (fun i : Fin m => singularValue A.transpose i.val ^ 2) := by
  simpa only [Matrix.transpose_transpose, leftVectorMatrix] using
    gram_basis_matrix_diagonal A.transpose (leftBasis A) (leftBasis_gram A)

theorem singularTailSq_step {m n : ℕ} (A : Rect m n) (r : ℕ) :
    singularTailSq A r = singularValue A r ^ 2 + singularTailSq A (r+1) := by
  classical
  by_cases hr : r < n
  · let i : Fin n := ⟨r, hr⟩
    have hset : Finset.univ.filter (fun j : Fin n => r ≤ j.val) =
        insert i (Finset.univ.filter (fun j : Fin n => r+1 ≤ j.val)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        by_cases he : j.val = r
        · left
          apply Fin.ext
          exact he
        · right
          omega
      · rintro (hj | hj)
        · subst j
          exact le_rfl
        · omega
    have hi : i ∉ Finset.univ.filter (fun j : Fin n => r+1 ≤ j.val) := by
      simp [i]
    unfold singularTailSq
    rw [hset, Finset.sum_insert hi]
  · have hzero : ∀ s, n ≤ s → Finset.univ.filter (fun i : Fin n => s ≤ i.val) = ∅ := by
      intro s hs
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have his := (Finset.mem_filter.mp hi).2
      omega
    have hsig := (singular_values_semantics A).2.2 r (by omega)
    simp only [singularTailSq, hzero r (by omega), hzero (r+1) (by omega),
      Finset.sum_empty, hsig, zero_pow (by decide : 2 ≠ 0), zero_add]

theorem singularValue_transpose {m n : ℕ} (A : Rect m n) (r : ℕ) :
    singularValue A.transpose r = singularValue A r := by
  have h1 := singularTailSq_step A r
  have h2 := singularTailSq_step A.transpose r
  rw [singularTailSq_transpose A r, singularTailSq_transpose A (r+1)] at h2
  have hpos1 := (singular_values_semantics A).1 r
  have hpos2 := (singular_values_semantics A.transpose).1 r
  nlinarith

#print axioms leftVectorMatrix_gram_diagonal
#print axioms singularValue_transpose
end
end Reference.RealOptimalityEquality
