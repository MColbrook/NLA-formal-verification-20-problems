module

public import NLA.TR27.PaperGeneralHankelDefinitions
public import NLA.TR27.PaperConfluent

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

theorem mul_signature_zero (r : ℕ) (B : Matrix (Fin (r+2)) (Fin (r+2)) ℂ)
    (i : Fin (r+2)) : (B * signatureMatrix r) i 0 = B i 1 := by
  simp [Matrix.mul_apply, signatureMatrix, mul_ite]

theorem mul_signature_one (r : ℕ) (B : Matrix (Fin (r+2)) (Fin (r+2)) ℂ)
    (i : Fin (r+2)) : (B * signatureMatrix r) i 1 = B i 0 := by
  simp [Matrix.mul_apply, signatureMatrix, mul_ite]

theorem mul_signature_tail (r : ℕ) (B : Matrix (Fin (r+2)) (Fin (r+2)) ℂ)
    (i : Fin (r+2)) (j : Fin r) :
    (B * signatureMatrix r) i j.succ.succ = -B i j.succ.succ := by
  simp [Matrix.mul_apply, signatureMatrix, mul_ite]

theorem signature_square (r : ℕ) : signatureMatrix r * signatureMatrix r = 1 := by
  ext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [mul_signature_zero]
    simp [signatureMatrix, Matrix.one_apply]
  · refine Fin.cases ?_ (fun j => ?_) j
    · rw [show (0 : Fin (r+1)).succ = 1 from rfl, mul_signature_one]
      simp [signatureMatrix, Matrix.one_apply]
    · rw [mul_signature_tail]
      by_cases h : i = j.succ.succ <;> simp [signatureMatrix, Matrix.one_apply, h]

theorem signature_det_ne_zero (r : ℕ) : (signatureMatrix r).det ≠ 0 := by
  intro hz
  have h := congrArg Matrix.det (signature_square r)
  rw [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at h
  exact zero_ne_one h

theorem tangent_hankel_entry (i j : ℕ) :
    (if i = 0 then (1 : ℂ) else 0) * (if j = 1 then 1 else 0) +
      (if i = 1 then (1 : ℂ) else 0) * (if j = 0 then 1 else 0) =
      if i+j = 1 then 1 else 0 := by
  split_ifs <;> norm_num at * <;> omega

theorem centerHankel_factorization (r : ℕ) (a : Fin r → ℂ) :
    centerHankel r a =
      confluentMatrix r a * signatureMatrix r * (confluentMatrix r a).transpose := by
  ext i j
  have hzero (i : Fin (r+2)) : confluentMatrix r a i 0 = if i.val = 1 then 1 else 0 := rfl
  have hone (i : Fin (r+2)) : confluentMatrix r a i 1 = if i.val = 0 then 1 else 0 := by
    change (0 : ℂ)^i.val = _
    exact zero_pow_eq _
  have htail (i : Fin (r+2)) (l : Fin r) :
      confluentMatrix r a i l.succ.succ = a l ^ i.val := rfl
  rw [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ,
    mul_signature_zero, show (0 : Fin (r+1)).succ = 1 from rfl, mul_signature_one]
  simp only [mul_signature_tail, Matrix.transpose_apply, hzero, hone, htail,
    neg_mul, ← pow_add, Finset.sum_neg_distrib]
  rw [← add_assoc, tangent_hankel_entry]
  rfl

theorem centerHankel_det_ne_zero (r : ℕ) (a : Fin r → ℂ)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) :
    (centerHankel r a).det ≠ 0 := by
  rw [centerHankel_factorization, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  exact mul_ne_zero (mul_ne_zero (confluent_det_ne_zero r a ha ha0)
    (signature_det_ne_zero r)) (confluent_det_ne_zero r a ha ha0)

theorem centerHankel_coordinates {D r : ℕ} (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) :
    sourceHankel (r+1) hD (projectionCenter D r (fun i => some (a i))) =
      centerHankel r a := by
  ext i j
  simp [sourceHankel, centerHankel, projectionCenter, tangentVector, curveVector,
    Finset.sum_apply]

#print axioms centerHankel_det_ne_zero
end NLA.TR27.Paper
