module

public import NLA.PF02.PaperSymmetricDiagonal
public import NLA.PF02.Rank
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace NLA.PF02.Paper

theorem symmetricIndex_card (n : ℕ) : Fintype.card (SymIndex n) = n*(n+1)/2 := by
  have hf (i : Fin n) : Fintype.card {p : SymIndex n // p.val.2 = i} = i.val+1 := by
    rw [Fintype.card_congr (secondFiberEquiv i)]
    simpa only [Finset.mem_Iic, Fin.card_Iic] using Fintype.card_coe (Finset.Iic i)
  have hc : Fintype.card (SymIndex n) = ∑ i : Fin n, (i.val+1) := by
    rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv (fun p : SymIndex n => p.val.2)),
      Fintype.card_sigma]
    simp only [hf]
  have hsum := Finset.sum_range_id_mul_two n
  have hr : (∑ i : Fin n, (i.val+1)) = ∑ i ∈ Finset.range n, (i+1) :=
    Fin.sum_univ_eq_sum_range (fun i => i+1) n
  rw [hr, Finset.sum_add_distrib] at hc
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hc
  have he : Fintype.card (SymIndex n) * 2 = n*(n+1) := by
    cases n with
    | zero => simp_all
    | succ n => simp only [Nat.add_sub_cancel] at hsum; nlinarith
  rw [← he, Nat.mul_div_cancel _ (by norm_num)]

def symmetricUnit (k : ℕ) (p : SymIndex k) : Matrix (Fin k) (Fin k) ℝ :=
  symmetricMatrix (Pi.single p 1)

theorem symmetricMatrix_sum {k : ℕ} (v : SymIndex k → ℝ) :
    symmetricMatrix v = ∑ p, v p • symmetricUnit k p := by
  have hv : (∑ p : SymIndex k, v p • Pi.single p (1 : ℝ)) = v := by
    ext q
    simp [Pi.single_apply, Pi.smul_apply, Finset.sum_apply]
  have h := map_sum (coordinatesEquiv (n := k) (R := ℝ)).symm
    (fun p => v p • Pi.single p (1 : ℝ)) Finset.univ
  rw [hv] at h
  simp only [map_smul] at h
  have h' := congrArg Subtype.val h
  have hequiv (w : SymIndex k → ℝ) :
      ((coordinatesEquiv (n := k) (R := ℝ)).symm w).val = symmetricMatrix w := rfl
  simpa only [symmetricUnit, Submodule.coe_sum, Submodule.coe_smul, hequiv] using h'

theorem trace_factor_symmetric_rank_le {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Matrix (Fin k) (Fin k) ℝ)
    (B : Fin q → Matrix (Fin k) (Fin k) ℝ)
    (hA : ∀ i, (A i).transpose = A i)
    (h : ∀ i j, Matrix.trace (A i * B j) = M i j) :
    M.rank ≤ k*(k+1)/2 := by
  let U : Matrix (Fin p) (SymIndex k) ℝ := fun i => symmetricCoordinates (A i)
  let V : Matrix (SymIndex k) (Fin q) ℝ := fun a j => Matrix.trace (symmetricUnit k a * B j)
  have heq : M = U * V := by
    ext i j
    change M i j = ∑ a, symmetricCoordinates (A i) a * Matrix.trace (symmetricUnit k a * B j)
    rw [← h i j]
    conv_lhs => rw [← matrix_coordinates (A i) (hA i), symmetricMatrix_sum]
    simp [U, V, Matrix.mul_apply, Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul]
  rw [heq]
  simpa only [symmetricIndex_card] using
    (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)

theorem factorization_symmetric_rank_le {p q k : ℕ} {M : Mat p q}
    (F : Factorization M k) : M.rank ≤ k*(k+1)/2 := by
  apply trace_factor_symmetric_rank_le M F.val.1 F.val.2 _ F.property.2.2
  intro i
  ext a b
  simpa only [Matrix.transpose_apply, star_trivial] using (F.property.1 i).isHermitian.apply a b

#print axioms factorization_symmetric_rank_le
end NLA.PF02.Paper
