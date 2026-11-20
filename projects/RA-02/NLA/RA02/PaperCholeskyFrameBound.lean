module

public import NLA.RA02.PaperCholeskyTailBound

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem exists_rotated_frame_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (R : NLA.RA02.Square n) (V : Matrix.unitaryGroup (Fin n) ℂ)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (v : Fin n → ℂ) (b c : ℝ)
    (hb : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i*Complex.normSq (v i) = b)
    (hc : 0 ≤ c) (hd : 0 < b+c)
    (hrot : (V : NLA.RA02.Square n).conjTranspose*R*(V : NLA.RA02.Square n) =
      diagonalPivotUpdate a v (b+c)) :
    ∃ U : Matrix (Fin n) (Fin (n-k+1)) ℂ, U.conjTranspose*U = 1 ∧
      (b+c)*(U.conjTranspose*R*U).trace.re ≤
        (b+c)*(∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), a i) + (∑ i, a i)*c := by
  obtain ⟨g,hg,hn,hbnd⟩ := diagonalPivotUpdate_exists_probe hk hkn a ha v b c hb hc hd
  let F := headTailFrame hkn g
  have hV : (V : NLA.RA02.Square n).conjTranspose*(V : NLA.RA02.Square n) = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  have hU : ((V : NLA.RA02.Square n)*F).conjTranspose*((V : NLA.RA02.Square n)*F) = 1 := by
    rw [Matrix.conjTranspose_mul]
    calc
      _ = F.conjTranspose*((V : NLA.RA02.Square n).conjTranspose*(V : NLA.RA02.Square n))*F := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV, Matrix.mul_one]; exact headTailFrame_orthonormal hkn g hg hn
  refine ⟨(V : NLA.RA02.Square n)*F,hU,?_⟩
  have he : ((V : NLA.RA02.Square n)*F).conjTranspose*R*((V : NLA.RA02.Square n)*F) =
      F.conjTranspose*((V : NLA.RA02.Square n).conjTranspose*R*(V : NLA.RA02.Square n))*F := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he, headTailFrame_trace, hrot, Complex.add_re, Complex.re_sum]
  have hsum : (∑ j : Fin (n-k), (diagonalPivotUpdate a v (b+c) (tailIndex k hkn j) (tailIndex k hkn j)).re) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), a i := by
    rw [← sum_tailIndex hkn]
    exact Finset.sum_le_sum (fun j _ => diagonalPivotUpdate_diag_le a v (b+c) hd.le _)
  have hm := mul_le_mul_of_nonneg_left hsum hd.le
  nlinarith

theorem exists_cholesky_frame_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A : NLA.RA02.Square n) (hA : A.PosSemidef) (V : Matrix.unitaryGroup (Fin n) ℂ)
    (hdiag : (V : NLA.RA02.Square n).conjTranspose*A*(V : NLA.RA02.Square n) =
      Matrix.diagonal (fun i => (NLA.RA02.orderedEigenvalues A hA.isHermitian i : ℂ)))
    (p : Fin n) (hp : A p p ≠ 0) :
    ∃ U : Matrix (Fin n) (Fin (n-k+1)) ℂ, U.conjTranspose*U = 1 ∧
      (A p p).re*(U.conjTranspose*NLA.RA02.choleskyStep A p*U).trace.re ≤
        (A p p).re*NLA.RA02.rankTail A hA.isHermitian k + NLA.RA02.realTrace A*
          (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val),
            NLA.RA02.orderedEigenvalues A hA.isHermitian i *
              Complex.normSq (star ((V : NLA.RA02.Square n) p i))) := by
  let a := NLA.RA02.orderedEigenvalues A hA.isHermitian
  let v := fun i => star ((V : NLA.RA02.Square n) p i)
  let b := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i*Complex.normSq (v i)
  let c := ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), a i*Complex.normSq (v i)
  have ha := NLA.RA02.orderedEigenvalues_nonneg A hA
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (Complex.normSq_nonneg _))
  have hpval : A p p = ((b+c : ℝ) : ℂ) := by
    rw [diagonalization_pivot A V a hdiag p, ← weighted_head_tail_split k a v]
  have hd : b+c ≠ 0 := by intro hz; apply hp; rw [hpval,hz,Complex.ofReal_zero]
  have hpd : (A p p).re = b+c := by rw [hpval, Complex.ofReal_re]
  have hdpos : 0 < b+c := lt_of_le_of_ne (hpd ▸ NLA.RA02.diagonal_real_nonneg hA p) (Ne.symm hd)
  have hr := rotate_choleskyStep A hA.isHermitian V a hdiag p (b+c) hpval hd
  obtain ⟨U,hU,hbnd⟩ := exists_rotated_frame_bound hk hkn (NLA.RA02.choleskyStep A p) V a ha v b c rfl hc hdpos hr
  refine ⟨U,hU,?_⟩
  have ht : (∑ i, a i) = NLA.RA02.realTrace A := (NLA.RA02.trace_eq_sum_ordered A hA.isHermitian).symm
  rw [ht] at hbnd
  rw [hpd]
  exact hbnd

#print axioms exists_cholesky_frame_bound
end NLA.RA02.Paper
