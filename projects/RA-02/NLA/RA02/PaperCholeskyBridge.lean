module

public import NLA.RA02.PaperResidualUpdate

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem complexify_cholesky_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) :
    NLA.RA02.choleskyStep (complexify A) j = complexify (crossUpdate A j j) := by
  by_cases hj : A j j = 0
  · ext a b
    simp [NLA.RA02.choleskyStep, complexify, crossUpdate, hj]
  · ext a b
    simp [NLA.RA02.choleskyStep, complexify, crossUpdate, hj]

theorem complexify_real_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    NLA.RA02.realTrace (complexify A) = A.trace := by
  simp [NLA.RA02.realTrace, complexify, Matrix.trace, Matrix.diag]

theorem complexify_cholesky_path {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (w : List (Fin n)) :
    NLA.RA02.pathResidual (complexify A) w = complexify (realCholeskyPath A w) := by
  induction w generalizing A with
  | nil => rfl
  | cons j w ih =>
    rw [NLA.RA02.pathResidual, complexify_cholesky_step, realCholeskyPath, ih]

theorem complexify_residual_update {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows : Fin s ↪ Fin n) (p : Fin n) (hp : p ∉ Set.range rows)
    (hu : IsUnit (A.submatrix rows rows))
    (ha : IsUnit (A.submatrix (appendEmbedding rows p hp) (appendEmbedding rows p hp))) :
    NLA.RA02.choleskyStep (complexify (interpolatoryResidual A rows rows)) p =
      complexify (interpolatoryResidual A (appendEmbedding rows p hp) (appendEmbedding rows p hp)) := by
  rw [complexify_cholesky_step, residual_append_update A rows rows p p hp hp hu ha]

#print axioms complexify_residual_update
end NLA.RA02.Paper
