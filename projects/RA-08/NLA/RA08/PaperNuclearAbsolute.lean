module

public import NLA.RA08.PaperNuclearFrobenius
public import NLA.RA08.PaperAbsoluteIdentities

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators MatrixOrder
namespace NLA.RA08.Paper

theorem nuclearNorm_hermitian {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    nuclearNorm A=(matrixAbsolute A).trace := by
  have ht : A.transpose=A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.eq
  have hs : cfc (fun x : ℝ => x*x) A=A*A := by
    rw [cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) A continuous_id.continuousOn continuous_id.continuousOn]
    have hid : cfc (fun x : ℝ => x) A=A := cfc_id' ℝ A hA
    rw [hid]
  have hc := cfc_comp Real.sqrt (fun x : ℝ => x*x) A hA (by fun_prop) (by fun_prop)
  have he : (Real.sqrt ∘ (fun x : ℝ => x*x))=abs := by
    funext x
    simpa only [Function.comp_def,pow_two] using Real.sqrt_sq_eq_abs x
  rw [he,hs] at hc
  unfold nuclearNorm matrixAbsolute functionalCalculus
  rw [ht,← hc]

theorem nuclearNorm_hermitian_spectral {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    nuclearNorm A=∑ i, |hA.eigenvalues i| := by
  rw [nuclearNorm_hermitian A hA]
  exact real_cfc_trace A hA abs

end NLA.RA08.Paper
