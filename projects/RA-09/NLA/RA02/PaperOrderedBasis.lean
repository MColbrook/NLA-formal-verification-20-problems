module

public import NLA.RA02.PaperKyFan

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem exists_ordered_eigenbasis {n : ℕ} (A : NLA.RA02.Square n) (hA : A.IsHermitian) :
    ∃ V : Matrix.unitaryGroup (Fin n) ℂ,
      (V : NLA.RA02.Square n).conjTranspose * A * (V : NLA.RA02.Square n) =
        Matrix.diagonal (fun i => (NLA.RA02.orderedEigenvalues A hA i : ℂ)) := by
  let U := hA.eigenvectorUnitary
  let e := NLA.RA02.eigenvalueReindex n
  let V : NLA.RA02.Square n := (U : NLA.RA02.Square n).submatrix id e
  have hU : (U : NLA.RA02.Square n).conjTranspose * (U : NLA.RA02.Square n) = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hU' : (U : NLA.RA02.Square n) * (U : NLA.RA02.Square n).conjTranspose = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  have hV : V.conjTranspose * V = 1 := by
    dsimp [V]
    rw [Matrix.conjTranspose_submatrix]
    rw [← Matrix.submatrix_mul _ _ e id e Function.bijective_id, hU]
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, e.injective.eq_iff]
  have hV' : V * V.conjTranspose = 1 := by
    dsimp [V]
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU']
    rfl
  refine ⟨⟨V, ?_⟩, ?_⟩
  · simpa only [Unitary.mem_iff, Matrix.star_eq_conjTranspose] using And.intro hV hV'
  · change V.conjTranspose * A * V = _
    have hspec : A = (U : NLA.RA02.Square n) *
        Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * (U : NLA.RA02.Square n).conjTranspose := by
      simpa [U, Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
        Function.comp_def] using hA.spectral_theorem
    have hd : (U : NLA.RA02.Square n).conjTranspose * A * (U : NLA.RA02.Square n) =
        Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
      conv_lhs => rw [hspec]
      calc
        _ = ((U : NLA.RA02.Square n).conjTranspose * (U : NLA.RA02.Square n)) *
          Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
          ((U : NLA.RA02.Square n).conjTranspose * (U : NLA.RA02.Square n)) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.one_mul, Matrix.mul_one]
    calc
      V.conjTranspose * A * V =
          ((U : NLA.RA02.Square n).conjTranspose * A * (U : NLA.RA02.Square n)).submatrix e e := by
        dsimp [V]
        rw [Matrix.conjTranspose_submatrix]
        rw [Matrix.submatrix_mul _ _ e id e Function.bijective_id]
        rw [Matrix.submatrix_mul _ _ e id id Function.bijective_id]
        rfl
      _ = _ := by
        rw [hd]
        ext i j
        simp [Matrix.submatrix_apply, Matrix.diagonal_apply, NLA.RA02.orderedEigenvalues_eq_reindexed,
          e, (NLA.RA02.eigenvalueReindex n).injective.eq_iff]

#print axioms exists_ordered_eigenbasis
end NLA.RA02.Paper
