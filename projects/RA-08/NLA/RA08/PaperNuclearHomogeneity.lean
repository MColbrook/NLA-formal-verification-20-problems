module

public import NLA.RA08.PaperNuclearVariational

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators MatrixOrder
namespace NLA.RA08.Paper

theorem matrixAbsolute_smul {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) (t : ℝ) :
    matrixAbsolute (t • A)=|t| • matrixAbsolute A := by
  have hid : cfc (fun x : ℝ => x) A=A := cfc_id' ℝ A hA
  have hs : cfc (fun x : ℝ => t*x) A=t • A := by
    simpa only [smul_eq_mul,hid] using cfc_smul t (fun x : ℝ => x) A continuous_id.continuousOn
  have hc := cfc_comp abs (fun x : ℝ => t*x) A hA (by fun_prop) (by fun_prop)
  have he : (abs ∘ (fun x : ℝ => t*x))=(fun x : ℝ => |t| • |x|) := by
    funext x
    exact abs_mul t x
  rw [he,hs,cfc_smul |t| abs A (by fun_prop)] at hc
  exact hc.symm

theorem nuclearNorm_hermitian_smul {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) (t : ℝ) :
    nuclearNorm (t • A)=|t| * nuclearNorm A := by
  have hTA : (t • A).IsHermitian := hA.smul (by simp [IsSelfAdjoint])
  rw [nuclearNorm_hermitian (t • A) hTA,matrixAbsolute_smul A hA t,Matrix.trace_smul,
    nuclearNorm_hermitian A hA]
  rfl

theorem nuclearNorm_hermitian_neg {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    nuclearNorm (-A)=nuclearNorm A := by
  have h := nuclearNorm_hermitian_smul A hA (-1)
  simpa using h

theorem nuclearNorm_hermitian_sub {n : ℕ} (A B : RealMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    nuclearNorm (A-B) ≤ nuclearNorm A+nuclearNorm B := by
  have h := nuclearNorm_hermitian_triangle A (-B) hA hB.neg
  simpa only [sub_eq_add_neg,nuclearNorm_hermitian_neg B hB] using h

end NLA.RA08.Paper
