module

public import NLA.PF02.PaperSymmetricCoordinates
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.PF02.Paper
variable {R : Type*} [CommRing R] {n : ℕ}

theorem congruenceMatrix_diagonal (d : Fin n → R) :
    congruenceMatrix (Matrix.diagonal d) = Matrix.diagonal (fun p : SymIndex n => d p.val.1 * d p.val.2) := by
  ext p q
  simp only [congruenceMatrix, LinearMap.toMatrix_apply, Pi.basisFun_apply,
    Pi.basisFun_repr, coordinateAction_apply, symmetricCoordinates,
    Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
    symmetricMatrix, dif_pos p.property]
  by_cases hpq : p = q
  · subst q
    simp
  · simp [hpq, Ne.symm hpq]

def firstFiberEquiv (i : Fin n) :
    {p : SymIndex n // p.val.1 = i} ≃ {j : Fin n // i ≤ j} where
  toFun p := ⟨p.val.val.2, by simpa only [p.property] using p.val.property⟩
  invFun j := ⟨⟨(i,j.val),j.property⟩,rfl⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext p.property.symm rfl
  right_inv j := rfl

def secondFiberEquiv (i : Fin n) :
    {p : SymIndex n // p.val.2 = i} ≃ {j : Fin n // j ≤ i} where
  toFun p := ⟨p.val.val.1, by simpa only [p.property] using p.val.property⟩
  invFun j := ⟨⟨(j.val,i),j.property⟩,rfl⟩
  left_inv p := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl p.property.symm
  right_inv j := rfl

theorem symmetric_diagonal_product (d : Fin n → R) :
    (∏ p : SymIndex n, d p.val.1 * d p.val.2) = (∏ i, d i)^(n+1) := by
  have hfirst (i : Fin n) : Fintype.card {p : SymIndex n // p.val.1 = i} = n-i.val := by
    rw [Fintype.card_congr (firstFiberEquiv i)]
    simpa only [Finset.mem_Ici, Fin.card_Ici] using Fintype.card_coe (Finset.Ici i)
  have hsecond (i : Fin n) : Fintype.card {p : SymIndex n // p.val.2 = i} = i.val+1 := by
    rw [Fintype.card_congr (secondFiberEquiv i)]
    simpa only [Finset.mem_Iic, Fin.card_Iic] using Fintype.card_coe (Finset.Iic i)
  rw [Finset.prod_mul_distrib,
    ← Fintype.prod_fiberwise' (fun p : SymIndex n => p.val.1) d,
    ← Fintype.prod_fiberwise' (fun p : SymIndex n => p.val.2) d]
  simp only [Finset.prod_const, Finset.card_univ, hfirst, hsecond]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← pow_add]
  congr 1
  omega

theorem congruenceMatrix_diagonal_det (d : Fin n → R) :
    (congruenceMatrix (Matrix.diagonal d)).det = (Matrix.diagonal d).det^(n+1) := by
  rw [congruenceMatrix_diagonal, Matrix.det_diagonal, Matrix.det_diagonal,
    symmetric_diagonal_product]

end NLA.PF02.Paper
