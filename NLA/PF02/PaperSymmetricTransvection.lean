module

public import NLA.PF02.PaperSymmetricCoordinates
public import Mathlib.Algebra.Polynomial.Degree.Units

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.PF02.Paper

theorem congruenceMatrix_map {R T : Type*} [CommRing R] [CommRing T] {n : ℕ}
    (f : R →+* T) (S : Matrix (Fin n) (Fin n) R) :
    (congruenceMatrix S).map f = congruenceMatrix (S.map f) := by
  ext p q
  simp [congruenceMatrix, LinearMap.toMatrix_apply, coordinateAction_apply,
    symmetricCoordinates, symmetricMatrix, Matrix.mul_apply, Matrix.map_apply,
    Matrix.transpose_apply, apply_dite, apply_ite, map_sum, map_mul, Pi.single_apply]

theorem transvection_map {R T : Type*} [CommRing R] [CommRing T] {n : ℕ}
    (f : R →+* T) (i j : Fin n) (c : R) :
    (Matrix.transvection i j c).map f = Matrix.transvection i j (f c) := by
  change f.mapMatrix (1 + Matrix.single i j c) = 1 + Matrix.single i j (f c)
  rw [map_add, map_one]
  congr 1
  exact Matrix.map_single i j c f

theorem congruence_transvection_polynomial_det {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (congruenceMatrix (Matrix.transvection i j (Polynomial.X : Polynomial ℝ))).det = 1 := by
  let A := congruenceMatrix (Matrix.transvection i j (Polynomial.X : Polynomial ℝ))
  let B := congruenceMatrix (Matrix.transvection i j (-Polynomial.X : Polynomial ℝ))
  have hab : A * B = 1 := by
    rw [← congruenceMatrix_mul]
    simp [Matrix.transvection_mul_transvection_same, hij, congruenceMatrix_one]
  have hu : IsUnit A.det := IsUnit.of_mul_eq_one B.det (by rw [← Matrix.det_mul, hab, Matrix.det_one])
  have hc : A.det = Polynomial.C (A.det.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero (Polynomial.natDegree_eq_zero_of_isUnit hu)
  have he : Polynomial.eval 0 A.det = 1 := by
    change (Polynomial.evalRingHom 0) A.det = 1
    rw [RingHom.map_det]
    change ((congruenceMatrix (Matrix.transvection i j (Polynomial.X : Polynomial ℝ))).map
      (Polynomial.evalRingHom 0)).det = 1
    rw [congruenceMatrix_map, transvection_map]
    simp [congruenceMatrix_one]
  rw [hc] at he ⊢
  simpa using congrArg Polynomial.C he

theorem congruence_transvection_det {n : ℕ} (i j : Fin n) (hij : i ≠ j) (c : ℝ) :
    (congruenceMatrix (Matrix.transvection i j c)).det = 1 := by
  have h := congrArg (Polynomial.evalRingHom c) (congruence_transvection_polynomial_det i j hij)
  rw [RingHom.map_det] at h
  change ((congruenceMatrix (Matrix.transvection i j (Polynomial.X : Polynomial ℝ))).map
    (Polynomial.evalRingHom c)).det = (Polynomial.evalRingHom c) 1 at h
  rw [congruenceMatrix_map, transvection_map] at h
  simpa using h

end NLA.PF02.Paper
