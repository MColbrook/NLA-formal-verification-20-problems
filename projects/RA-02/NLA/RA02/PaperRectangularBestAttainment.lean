module

public import NLA.RA02.PaperRectangularBestLower

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem rectangular_frobenius_unitary_right {m n : ℕ}
    (E : Matrix (Fin m) (Fin n) ℂ) (V : Matrix.unitaryGroup (Fin n) ℂ) :
    NLA.RA03.frobeniusSq (E*(V : NLA.RA02.Square n)) = NLA.RA03.frobeniusSq E := by
  rw [lu_frobeniusSq_eq_gram_trace,lu_frobeniusSq_eq_gram_trace]
  have hV : (V : NLA.RA02.Square n)*(V : NLA.RA02.Square n).conjTranspose = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self V
  have he : (E*(V : NLA.RA02.Square n)).conjTranspose*(E*(V : NLA.RA02.Square n)) =
      (V : NLA.RA02.Square n).conjTranspose*(E.conjTranspose*E)*(V : NLA.RA02.Square n) := by
    simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  rw [he,NLA.RA02.realTrace, NLA.RA02.realTrace,Matrix.trace_mul_cycle,hV,Matrix.one_mul]

theorem rectangular_best_error_attained {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) :
    ∃ B : Matrix (Fin m) (Fin n) ℂ, B.rank ≤ r ∧
      NLA.RA03.frobeniusSq (A-B) = gramTail A r := by
  let G := A.conjTranspose*A
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  obtain ⟨V,hdiag⟩ := exists_ordered_eigenbasis G hG.isHermitian
  let a := NLA.RA02.orderedEigenvalues G hG.isHermitian
  let head : Fin n → ℂ := fun i => if i.val < r then 1 else 0
  let tail : Fin n → ℂ := fun i => if i.val < r then 0 else 1
  let B := A*(V : NLA.RA02.Square n)*Matrix.diagonal head*(V : NLA.RA02.Square n).conjTranspose
  have hRank : (Matrix.diagonal head).rank ≤ r := by
    rw [Matrix.rank_diagonal]
    let f : {i : Fin n // head i ≠ 0} → Fin r := fun i =>
      ⟨i.val.val,by simpa [head] using i.property⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Subtype.ext
      apply Fin.ext
      exact congrArg (fun x : Fin r => x.val) hij
    exact (Fintype.card_le_of_injective f hf).trans_eq (Fintype.card_fin r)
  have hV : (V : NLA.RA02.Square n)*(V : NLA.RA02.Square n).conjTranspose = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self V
  have hmask : (1 : NLA.RA02.Square n)-Matrix.diagonal head = Matrix.diagonal tail := by
    ext i j
    by_cases hij : i=j
    · subst j
      by_cases hi : i.val < r <;> simp [Matrix.one_apply,Matrix.diagonal_apply,head,tail,hi]
    · simp [Matrix.one_apply,Matrix.diagonal_apply,hij,Ne.symm hij]
  have he : A-B = A*(V : NLA.RA02.Square n)*Matrix.diagonal tail*(V : NLA.RA02.Square n).conjTranspose := by
    have hA : A = A*(V : NLA.RA02.Square n)*(1 : NLA.RA02.Square n)*(V : NLA.RA02.Square n).conjTranspose := by
      rw [Matrix.mul_one,Matrix.mul_assoc,hV,Matrix.mul_one]
    change A - A*(V : NLA.RA02.Square n)*Matrix.diagonal head*(V : NLA.RA02.Square n).conjTranspose = _
    conv_lhs => lhs; rw [hA]
    rw [← Matrix.sub_mul,← Matrix.mul_sub,hmask]
  refine ⟨B,(Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hRank),?_⟩
  rw [he]
  have hstar : (V : NLA.RA02.Square n).conjTranspose = (star V : Matrix.unitaryGroup (Fin n) ℂ) := by
    simp only [Unitary.coe_star,Matrix.star_eq_conjTranspose]
  rw [hstar,rectangular_frobenius_unitary_right,lu_frobeniusSq_eq_gram_trace]
  have ht : (Matrix.diagonal tail).conjTranspose = Matrix.diagonal tail := by
    ext i j
    by_cases hij : i=j
    · subst j
      by_cases hi : i.val < r <;> simp [Matrix.conjTranspose_apply,Matrix.diagonal_apply,tail,hi]
    · simp [Matrix.conjTranspose_apply,Matrix.diagonal_apply,hij,Ne.symm hij]
  have hg : (A*(V : NLA.RA02.Square n)*Matrix.diagonal tail).conjTranspose*
      (A*(V : NLA.RA02.Square n)*Matrix.diagonal tail) =
      Matrix.diagonal tail*((V : NLA.RA02.Square n).conjTranspose*G*(V : NLA.RA02.Square n))*Matrix.diagonal tail := by
    simp only [Matrix.conjTranspose_mul,ht,Matrix.mul_assoc,G]
  rw [hg,hdiag,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal,NLA.RA02.realTrace,Matrix.trace_diagonal,Complex.re_sum]
  change (∑ i, (tail i*(a i : ℂ)*tail i).re) =
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ i.val), a i
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r
  · simp [tail,hi,show ¬ r ≤ i.val from by omega]
  · simp [tail,hi,show r ≤ i.val from by omega]

theorem rectangularBest_eq_gramTail {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) :
    rectangularBestRankErrorSquared A r = gramTail A r := by
  apply le_antisymm
  · obtain ⟨B,hB,he⟩ := rectangular_best_error_attained A r
    apply csInf_le
    · refine ⟨0,?_⟩
      rintro e ⟨C,_,hc⟩
      rw [← hc]
      exact lu_frobeniusSq_nonneg _
    · exact ⟨B,hB,he⟩
  · exact gramTail_le_rectangularBest A r

#print axioms rectangularBest_eq_gramTail
end NLA.RA02.Paper
