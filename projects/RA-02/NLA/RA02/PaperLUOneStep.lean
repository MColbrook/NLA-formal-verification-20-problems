module

public import NLA.RA02.PaperLUProcess

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem lu_unnormalized_tail_bound {m n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (∑ i, ∑ j, Complex.normSq (A i j)*gramTail (NLA.RA03.pivotResidual A (i,j)) (k-1)) ≤
      4*NLA.RA03.frobeniusSq A*gramTail A k := by
  let G := A.conjTranspose*A
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  obtain ⟨V,hV⟩ := exists_ordered_eigenbasis G hG.isHermitian
  let c := fun j => ∑ l ∈ Finset.univ.filter (fun l : Fin n => k ≤ l.val),
    NLA.RA02.orderedEigenvalues G hG.isHermitian l*Complex.normSq (star ((V : NLA.RA02.Square n) j l))
  have hc : (∑ j, c j) = gramTail A k := sum_pivot_tail_weights V _ k
  have hd : (∑ j : Fin n, 2*(G j j).re*gramTail A k) =
      2*NLA.RA02.realTrace G*gramTail A k := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← NLA.RA02.realTrace_eq_sum]
  have hcSum : (∑ j : Fin n, 2*NLA.RA02.realTrace G*c j) =
      2*NLA.RA02.realTrace G*gramTail A k := by
    rw [← Finset.mul_sum,hc]
  have hb := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
    lu_column_tail_bound hk hkn A V hV j)
  change (∑ j, ∑ i, Complex.normSq (A i j)*gramTail (NLA.RA03.pivotResidual A (i,j)) (k-1)) ≤
    ∑ j, (2*(G j j).re*gramTail A k + 2*NLA.RA02.realTrace G*c j) at hb
  rw [Finset.sum_add_distrib,hd,hcSum,Finset.sum_comm] at hb
  rw [lu_frobeniusSq_eq_gram_trace]
  linarith

theorem lu_one_step_tail_bound {m n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) :
    (∑ p : NLA.RA03.Pivot m n, NLA.RA03.pivotMass A p*gramTail (NLA.RA03.nextResidual A p) (k-1)) ≤
      4*gramTail A k := by
  by_cases hA : A = 0
  · subst A
    have hnext : ∀ p : NLA.RA03.Pivot m n, NLA.RA03.nextResidual (0 : Matrix (Fin m) (Fin n) ℂ) p = 0 := by
      intro p
      cases p <;> simp [NLA.RA03.nextResidual, NLA.RA03.pivotResidual]
    simp_rw [hnext, gramTail_zero, mul_zero, Finset.sum_const_zero]
    exact le_refl 0
  · have hfne : NLA.RA03.frobeniusSq A ≠ 0 := fun hz => hA ((lu_frobeniusSq_eq_zero_iff A).mp hz)
    have hfpos : 0 < NLA.RA03.frobeniusSq A := lt_of_le_of_ne (lu_frobeniusSq_nonneg A) (Ne.symm hfne)
    rw [Fintype.sum_option]
    simp only [NLA.RA03.pivotMass, if_neg hA, NLA.RA03.nextResidual, zero_mul, zero_add]
    rw [Fintype.sum_prod_type]
    have he : (∑ i, ∑ j, Complex.normSq (A i j)/NLA.RA03.frobeniusSq A *
        gramTail (NLA.RA03.pivotResidual A (i,j)) (k-1)) =
        (∑ i, ∑ j, Complex.normSq (A i j)*gramTail (NLA.RA03.pivotResidual A (i,j)) (k-1)) /
          NLA.RA03.frobeniusSq A := by
      simp only [div_mul_eq_mul_div, Finset.sum_div]
    rw [he]
    apply (div_le_iff₀ hfpos).mpr
    have hb := lu_unnormalized_tail_bound hk hkn A
    nlinarith

#print axioms lu_one_step_tail_bound
end NLA.RA02.Paper
