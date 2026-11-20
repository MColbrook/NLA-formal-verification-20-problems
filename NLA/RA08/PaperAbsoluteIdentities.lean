module

public import NLA.RA08.PaperAbsoluteFrobenius
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical MatrixOrder Matrix
namespace NLA.RA08.Paper

theorem matrixAbsolute_square {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    matrixAbsolute A*matrixAbsolute A=A*A := by
  unfold matrixAbsolute functionalCalculus
  rw [← cfc_mul abs abs A (by fun_prop) (by fun_prop)]
  have he : (fun x : ℝ => |x| * |x|)=(fun x => x*x) := by
    funext x
    simpa only [pow_two] using sq_abs x
  rw [he]
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA
  have hm := cfc_mul (fun x : ℝ => x) (fun x : ℝ => x) A
    continuous_id.continuousOn continuous_id.continuousOn
  rw [hm,hid]

theorem matrixAbsolute_hermitian {n : ℕ} (A : RealMatrix n) :
    (matrixAbsolute A).IsHermitian := cfc_predicate abs A

theorem scalar_clipping_absolute (x : ℝ) :
    witnessFunction x=(1/2 : ℝ)*(x+1-|x-1|) := by
  by_cases hx : x ≤ 1
  · rw [witnessFunction,min_eq_left hx,abs_of_nonpos (by linarith : x-1 ≤ 0)]
    ring
  · rw [witnessFunction,min_eq_right (le_of_not_ge hx),abs_of_pos (by linarith : 0 < x-1)]
    ring

theorem matrixAbsolute_shift {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    matrixAbsolute (A-1)=functionalCalculus (fun x : ℝ => |x-1|) A := by
  have hg : cfc (fun x : ℝ => x-1) A=A-1 := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ => (1 : ℝ)) A
      continuous_id.continuousOn continuous_const.continuousOn]
    have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA
    have h1 : cfc (fun _ : ℝ => 1) A = 1 := cfc_const_one ℝ A
    rw [hid,h1]
  have hc := cfc_comp abs (fun x : ℝ => x-1) A hA (by fun_prop) (by fun_prop)
  simpa only [matrixAbsolute,functionalCalculus,Function.comp_def,hg] using hc.symm

theorem matrix_clipping_absolute {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    functionalCalculus witnessFunction A = (1/2 : ℝ) • (A+1-matrixAbsolute (A-1)) := by
  have he : witnessFunction=(fun x : ℝ => (1/2 : ℝ) • (x+1-|x-1|)) := by
    funext x
    exact scalar_clipping_absolute x
  rw [functionalCalculus,he,cfc_smul (1/2 : ℝ) (fun x : ℝ => x+1-|x-1|) A (by fun_prop)]
  rw [cfc_sub (fun x : ℝ => x+1) (fun x => |x-1|) A (by fun_prop) (by fun_prop)]
  rw [cfc_add A (fun x : ℝ => x) (fun _ => (1 : ℝ))
    continuous_id.continuousOn continuous_const.continuousOn]
  have hid : cfc (fun x : ℝ => x) A = A := cfc_id' ℝ A hA
  have h1 : cfc (fun _ : ℝ => 1) A = 1 := cfc_const_one ℝ A
  rw [hid,h1]
  have hs : matrixAbsolute (A-1)=cfc (fun x : ℝ => |x-1|) A := matrixAbsolute_shift A hA
  rw [← hs]

#print axioms matrix_clipping_absolute
end NLA.RA08.Paper
