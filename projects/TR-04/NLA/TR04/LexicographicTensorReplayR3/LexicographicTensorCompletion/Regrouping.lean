module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual nested finite tensor regrouping, inverse, norm and multiplication identities.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorCompletion.Definitions
public import NLA.TR04.ThreeModeCompletion.FiniteMatrix

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage Reference.TensorGrouping
open scoped Matrix Kronecker

theorem merge_unmerge {m n : ℕ} {ns : List ℕ} (A : Tensor (rowCount m n) ns) :
    merge (unmerge (m:=m) (n:=n) A) = A := by
  ext i j
  simp [merge,unmerge]

theorem unmerge_merge {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) :
    unmerge (m:=m) (n:=n) (merge A) = A := by
  ext i j
  rcases j with ⟨j,l⟩
  simp [merge,unmerge]

theorem merge_sub {m n : ℕ} {ns : List ℕ} (A B : Tensor m (n::ns)) :
    merge (A-B) = merge A-merge B := rfl

theorem merge_mul {m k n : ℕ} {ns : List ℕ} (V : Rect k m) (A : Tensor m (n::ns)) :
    merge (V*A) = mergeLeft (n:=n) V * merge A := by
  let A0 : Matrix (Fin m) (Fin n × ModeIndex ns) ℝ := A
  change (grouped (V*A0)).submatrix (rowEquiv k n).symm id =
    (V ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℝ)).submatrix (rowEquiv k n).symm (rowEquiv m n).symm *
    (grouped A0).submatrix (rowEquiv m n).symm id
  rw [grouped_mul V A0]
  exact (Matrix.submatrix_mul_equiv _ _ _ _ _).symm

theorem merge_frobeniusSq {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) :
    tensorFrobeniusSq (merge A) = tensorFrobeniusSq A := by
  change entryFrobeniusSq (merge A) = entryFrobeniusSq A
  calc
    _ = entryFrobeniusSq (grouped A) :=
      Reference.ThreeModeCompletion.entryFrobeniusSq_submatrix_equiv (grouped A)
        (rowEquiv m n).symm (Equiv.refl _)
    _ = _ := grouped_frobeniusSq A

theorem unmerge_frobeniusSq {m n : ℕ} {ns : List ℕ} (A : Tensor (rowCount m n) ns) :
    tensorFrobeniusSq (unmerge (m:=m) (n:=n) A) = tensorFrobeniusSq A := by
  have h := merge_frobeniusSq (unmerge (m:=m) (n:=n) A)
  rw [merge_unmerge] at h
  exact h.symm

#print axioms merge_mul
#print axioms merge_frobeniusSq
#print axioms unmerge_merge
end
end Reference.LexTensorCompletion
