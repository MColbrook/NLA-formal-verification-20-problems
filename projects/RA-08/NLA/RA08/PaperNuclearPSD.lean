module

public import NLA.RA08.PaperNuclearAbsolute

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearNorm_posSemidef {n : ℕ} (A : RealMatrix n) (hA : A.PosSemidef) :
    nuclearNorm A=A.trace := by
  rw [nuclearNorm_hermitian_spectral A hA.isHermitian]
  have ht : A.trace=∑ i, hA.isHermitian.eigenvalues i := by
    simpa using hA.isHermitian.trace_eq_sum_eigenvalues
  rw [ht]
  apply Finset.sum_congr rfl
  intro i _
  exact abs_of_nonneg (hA.eigenvalues_nonneg i)

theorem nuclear_unit_outer_norm {n : ℕ} (v : Fin n → ℝ)
    (hv : ∑ i, (v i)^2=1) : nuclearNorm (Matrix.vecMulVec v v)=1 := by
  have he : Matrix.vecMulVec v v=Matrix.vecMulVec v (star v) := by
    ext i j
    simp [Matrix.vecMulVec]
  have hP : (Matrix.vecMulVec v v).PosSemidef := by
    rw [he]
    exact Matrix.posSemidef_vecMulVec_self_star v
  rw [nuclearNorm_posSemidef _ hP]
  simpa only [Matrix.trace,Matrix.diag,Matrix.vecMulVec,Matrix.of_apply,pow_two] using hv

end NLA.RA08.Paper
