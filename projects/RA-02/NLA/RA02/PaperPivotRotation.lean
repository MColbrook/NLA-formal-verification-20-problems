module

public import NLA.RA02.PaperOrderedBasis
public import NLA.RA02.PaperDiagonalUpdate
public import NLA.RA02.PivotAlgebra

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem rotate_outer {n : ℕ} (V : NLA.RA02.Square n) (x : Fin n → ℂ) :
    V.conjTranspose * Matrix.vecMulVec x (star x) * V =
      Matrix.vecMulVec (V.conjTranspose *ᵥ x) (star (V.conjTranspose *ᵥ x)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 1
  ext j
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    Pi.star_apply, star_sum, star_mul, star_star]

theorem choleskyStep_outer {n : ℕ} (A : NLA.RA02.Square n) (hA : A.IsHermitian)
    (p : Fin n) (hp : A p p ≠ 0) :
    NLA.RA02.choleskyStep A p = A - (A p p)⁻¹ •
      Matrix.vecMulVec (fun i => A i p) (star (fun i => A i p)) := by
  ext i j
  have hs : star (A j p) = A p j := congrFun (congrFun hA p) j
  simp only [NLA.RA02.choleskyStep, hp, if_false, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Pi.star_apply, hs]
  ring

theorem rotate_choleskyStep {n : ℕ} (A : NLA.RA02.Square n) (hA : A.IsHermitian)
    (V : Matrix.unitaryGroup (Fin n) ℂ) (a : Fin n → ℝ)
    (hdiag : (V : NLA.RA02.Square n).conjTranspose * A * (V : NLA.RA02.Square n) =
      Matrix.diagonal (fun i => (a i : ℂ))) (p : Fin n) (d : ℝ)
    (hd : A p p = (d : ℂ)) (hp : d ≠ 0) :
    (V : NLA.RA02.Square n).conjTranspose * NLA.RA02.choleskyStep A p * (V : NLA.RA02.Square n) =
      diagonalPivotUpdate a (fun i => star ((V : NLA.RA02.Square n) p i)) d := by
  have hV : (V : NLA.RA02.Square n)*(V : NLA.RA02.Square n).conjTranspose = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self V
  have he : (V : NLA.RA02.Square n).conjTranspose*A =
      Matrix.diagonal (fun i => (a i : ℂ))*(V : NLA.RA02.Square n).conjTranspose := by
    rw [← hdiag, Matrix.mul_assoc, Matrix.mul_assoc, hV, Matrix.mul_one]
  have hc : (V : NLA.RA02.Square n).conjTranspose *ᵥ (fun i => A i p) =
      fun i => (a i : ℂ)*star ((V : NLA.RA02.Square n) p i) := by
    ext i
    have hh := congrFun (congrFun he i) p
    rw [Matrix.diagonal_mul] at hh
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.mulVec, dotProduct] using hh
  have hp' : A p p ≠ 0 := by rw [hd]; exact_mod_cast hp
  rw [choleskyStep_outer A hA p hp', Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, hdiag, rotate_outer, hc, hd]
  rfl

#print axioms rotate_choleskyStep
end NLA.RA02.Paper
