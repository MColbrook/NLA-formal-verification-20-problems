module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual finite-index matrix best-rank attainment and orthogonal error identity.
Extends the checked real MI13/RA02 and concrete grouped-unfolding proofs.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.TensorGrouping

@[expose] public section

set_option autoImplicit false
namespace Reference.ThreeModeCompletion
noncomputable section
open Reference.RealSVDPackage Reference.RealColumnCompression Reference.TensorGrouping
open scoped BigOperators Matrix

theorem entryFrobeniusSq_submatrix_equiv {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (A : Matrix α β ℝ) (em : γ ≃ α) (en : δ ≃ β) :
    entryFrobeniusSq (A.submatrix em en) = entryFrobeniusSq A := by
  simp only [entryFrobeniusSq, Matrix.submatrix_apply]
  calc
    _ = ∑ i, ∑ j : δ, A i (en j) ^ 2 := em.sum_comp (fun i => ∑ j : δ, A i (en j)^2)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      exact en.sum_comp (fun j => A i j^2)

theorem finite_best_rank_frobenius_attainment {α β : Type*}
    [Fintype α] [Fintype β] (A : Matrix α β ℝ) (r : ℕ) :
    ∃ B : Matrix α β ℝ, B.rank ≤ r ∧
      ∀ C : Matrix α β ℝ, C.rank ≤ r →
        entryFrobeniusSq (A-B) ≤ entryFrobeniusSq (A-C) := by
  classical
  let em := Fintype.equivFin α
  let en := Fintype.equivFin β
  let A' : Rect (Fintype.card α) (Fintype.card β) := A.submatrix em.symm en.symm
  obtain ⟨B', hB', he, hmin⟩ := real_best_rank_frobenius_attainment A' r
  let B := B'.submatrix em en
  refine ⟨B, (Matrix.rank_submatrix_le B' em en).trans hB', ?_⟩
  intro C hC
  let C' : Rect (Fintype.card α) (Fintype.card β) := C.submatrix em.symm en.symm
  have hC' : C'.rank ≤ r := (Matrix.rank_submatrix_le C em.symm en.symm).trans hC
  have hAB : A-B = (A'-B').submatrix em en := by
    ext i j
    simp [A', B]
  have hAC : A'-C' = (A-C).submatrix em.symm en.symm := rfl
  calc
    _ = frobeniusSq (A'-B') := by rw [hAB, entryFrobeniusSq_submatrix_equiv]; rfl
    _ ≤ frobeniusSq (A'-C') := hmin C' hC'
    _ = _ := by
      change entryFrobeniusSq (A'-C') = _
      rw [hAC, entryFrobeniusSq_submatrix_equiv]

theorem finite_orthonormal_column_error_decomposition {β : Type*} [Fintype β]
    {m k : ℕ} (U : Rect m k) (hU : U.transpose * U = 1)
    (A : Matrix (Fin m) β ℝ) (C : Matrix (Fin k) β ℝ) :
    entryFrobeniusSq (A-U*C) = entryFrobeniusSq (A-U*U.transpose*A) +
      entryFrobeniusSq (U.transpose*A-C) := by
  classical
  let e := Fintype.equivFin β
  let A' : Rect m (Fintype.card β) := A.submatrix id e.symm
  let C' : Rect k (Fintype.card β) := C.submatrix id e.symm
  have h := orthonormal_column_error_decomposition U hU A' C'
  change entryFrobeniusSq (A'-U*C') = entryFrobeniusSq (A'-U*U.transpose*A') +
    entryFrobeniusSq (U.transpose*A'-C') at h
  have ha : A'-U*C' = (A-U*C).submatrix id e.symm := rfl
  have hb : A'-U*U.transpose*A' = (A-U*U.transpose*A).submatrix id e.symm := rfl
  have hc : U.transpose*A'-C' = (U.transpose*A-C).submatrix id e.symm := rfl
  rw [ha, hb, hc, entryFrobeniusSq_reindex_columns,
    entryFrobeniusSq_reindex_columns, entryFrobeniusSq_reindex_columns] at h
  exact h

#print axioms finite_best_rank_frobenius_attainment
#print axioms finite_orthonormal_column_error_decomposition
end
end Reference.ThreeModeCompletion
