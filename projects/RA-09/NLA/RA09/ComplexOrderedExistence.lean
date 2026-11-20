module

/- Complex-field adaptation of the credited real ordered spectral existence proof. -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical counterexample: Matthew J. Colbrook. This helper transports
Mathlib's genuine spectral theorem to the reviewed ordered-data interface.
-/
/- Adapted with attribution from the campaign reviewed RA-08 OrderedExistence.lean
source SHA256 4da2bb55befc17bca7d520fbae186aafede693927bcb2768e810790a0a3de37b.
The RA09 definitions are the independently approved local boundary; no RA08
implementation object or Challenge theorem is imported. -/
public import NLA.RA09.ComplexDefinitions
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Order.Fin.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Classical MatrixOrder ComplexOrder
noncomputable section

namespace NLA.RA09.ComplexPaper

/-- Every actual complex Hermitian PSD matrix has complete decreasing spectral data.
The order-preserving cardinality transport is followed by the inverse of
Mathlib's arbitrary eigenvalue reindexing. No eigenvalue is discarded, and
no positive dimension or distinct-eigenvalue assumption is used. -/
theorem orderedSpectral_exists_proved {n : ℕ} (A : ComplexMatrix n)
    (hA : A.PosSemidef) : Nonempty (OrderedSpectralData A) := by
  let h := hA.isHermitian
  let c : Fin n ≃o Fin (Fintype.card (Fin n)) :=
    Fin.castOrderIso (Fintype.card_fin n).symm
  let e₀ : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  let e : Fin n ≃ Fin n := c.toEquiv.trans e₀
  have heigen (i : Fin n) : h.eigenvalues (e i) = h.eigenvalues₀ (c i) := by
    simp [Matrix.IsHermitian.eigenvalues, e, e₀]
  let b := h.eigenvectorBasis.reindex e.symm
  let Q : Matrix.unitaryGroup (Fin n) ℂ :=
    ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix b.toBasis,
      (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
  have hQ (i j : Fin n) : (Q : ComplexMatrix n) i j = h.eigenvectorUnitary i (e j) := by
    change (b j) i = (h.eigenvectorBasis (e j)) i
    simp [b]
  refine ⟨{
    eigenvalues := fun i => h.eigenvalues (e i)
    unitary := Q
    decreasing := ?_
    nonnegative := fun i => hA.eigenvalues_nonneg (e i)
    reconstruct := ?_ }⟩
  · intro i j hij
    change h.eigenvalues (e j) ≤ h.eigenvalues (e i)
    rw [heigen, heigen]
    exact h.eigenvalues₀_antitone (c.monotone hij)
  · have hspec : A =
        (h.eigenvectorUnitary : ComplexMatrix n) * Matrix.diagonal (fun i => (h.eigenvalues i : ℂ)) *
          (h.eigenvectorUnitary : ComplexMatrix n).conjTranspose := by
      simpa [Unitary.conjStarAlgAut_apply,
        Matrix.star_eq_conjTranspose, 
        Function.comp_def]
        using h.spectral_theorem
    have hentry (U : ComplexMatrix n) (a : Fin n → ℝ) (i j : Fin n) :
        (U * Matrix.diagonal (fun i => (a i : ℂ)) * U.conjTranspose) i j =
          ∑ k, U i k * (a k : ℂ) * star (U j k) := by
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    refine hspec.trans ?_
    ext i j
    rw [hentry, hentry]
    simp_rw [hQ]
    exact (Equiv.sum_comp e (fun k =>
      h.eigenvectorUnitary i k * (h.eigenvalues k : ℂ) * star (h.eigenvectorUnitary j k))).symm

#print axioms orderedSpectral_exists_proved

end NLA.RA09.ComplexPaper
