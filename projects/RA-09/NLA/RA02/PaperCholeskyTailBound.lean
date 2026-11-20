module

public import NLA.RA02.PaperPivotRotation
public import NLA.RA02.PaperPivotWeights
public import NLA.RA02.PaperOneStepTail
public import NLA.RA02.PivotKernel

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem cholesky_pivot_tail_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A : NLA.RA02.Square n) (hA : A.PosSemidef) (hne : A ≠ 0)
    (V : Matrix.unitaryGroup (Fin n) ℂ)
    (hdiag : (V : NLA.RA02.Square n).conjTranspose*A*(V : NLA.RA02.Square n) =
      Matrix.diagonal (fun i => (NLA.RA02.orderedEigenvalues A hA.isHermitian i : ℂ))) (p : Fin n) :
    NLA.RA02.pivotMass A p * NLA.RA02.rankTail (NLA.RA02.choleskyStep A p)
      (NLA.RA02.choleskyStep_posSemidef A hA p).isHermitian (k-1) ≤
    NLA.RA02.pivotMass A p * NLA.RA02.rankTail A hA.isHermitian k +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val),
        NLA.RA02.orderedEigenvalues A hA.isHermitian i *
          Complex.normSq (star ((V : NLA.RA02.Square n) p i)) := by
  let a := NLA.RA02.orderedEigenvalues A hA.isHermitian
  let v := fun i => star ((V : NLA.RA02.Square n) p i)
  let b := ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i*Complex.normSq (v i)
  let c := ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), a i*Complex.normSq (v i)
  have ha := NLA.RA02.orderedEigenvalues_nonneg A hA
  have hc : 0 ≤ c := Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (Complex.normSq_nonneg _))
  have hp : A p p = ((b+c : ℝ) : ℂ) := by
    rw [diagonalization_pivot A V a hdiag p, ← weighted_head_tail_split k a v]
  have hpd : (A p p).re = b+c := by rw [hp, Complex.ofReal_re]
  have htrace := NLA.RA02.realTrace_pos hA hne
  have hm : NLA.RA02.pivotMass A p = (b+c)/NLA.RA02.realTrace A := by
    simp only [NLA.RA02.pivotMass, if_neg (ne_of_gt htrace), hpd]
  by_cases hd : b+c = 0
  · rw [hm, hd, zero_div, zero_mul, zero_mul, zero_add]
    exact hc
  · have hdpos : 0 < b+c := lt_of_le_of_ne (hpd ▸ NLA.RA02.diagonal_real_nonneg hA p) (Ne.symm hd)
    have hr := rotate_choleskyStep A hA.isHermitian V a hdiag p (b+c) hp hd
    have hbnd := rotated_tail_bound hk hkn (NLA.RA02.choleskyStep A p)
      (NLA.RA02.choleskyStep_posSemidef A hA p) V a ha v b c rfl hc hdpos hr
    have ht : (∑ i, a i) = NLA.RA02.realTrace A := (NLA.RA02.trace_eq_sum_ordered A hA.isHermitian).symm
    rw [ht] at hbnd
    change (b+c)*_ ≤ (b+c)*NLA.RA02.rankTail A hA.isHermitian k + NLA.RA02.realTrace A*c at hbnd
    rw [hm]
    change (b+c)/NLA.RA02.realTrace A*_ ≤ (b+c)/NLA.RA02.realTrace A*_ + c
    have hdiv := (div_le_div_iff_of_pos_right htrace).mpr hbnd
    have hx : (b+c)*NLA.RA02.rankTail (NLA.RA02.choleskyStep A p)
        (NLA.RA02.choleskyStep_posSemidef A hA p).isHermitian (k-1) / NLA.RA02.realTrace A =
        (b+c)/NLA.RA02.realTrace A * NLA.RA02.rankTail (NLA.RA02.choleskyStep A p)
        (NLA.RA02.choleskyStep_posSemidef A hA p).isHermitian (k-1) := by ring
    have hy : ((b+c)*NLA.RA02.rankTail A hA.isHermitian k + NLA.RA02.realTrace A*c) /
        NLA.RA02.realTrace A = (b+c)/NLA.RA02.realTrace A*NLA.RA02.rankTail A hA.isHermitian k + c := by
      field_simp [ne_of_gt htrace]
    rw [hx, hy] at hdiv
    exact hdiv

theorem rankTail_le_trace {n : ℕ} (A : NLA.RA02.Square n) (hA : A.PosSemidef) (k : ℕ) :
    NLA.RA02.rankTail A hA.isHermitian k ≤ NLA.RA02.realTrace A := by
  rw [NLA.RA02.trace_eq_sum_ordered]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => NLA.RA02.orderedEigenvalues_nonneg A hA i)

theorem rankTail_zero_matrix {n : ℕ} (h : (0 : NLA.RA02.Square n).PosSemidef) (k : ℕ) :
    NLA.RA02.rankTail 0 h.isHermitian k = 0 := by
  apply le_antisymm
  · simpa using rankTail_le_trace 0 h k
  · exact NLA.RA02.rankTail_nonneg 0 h k

theorem cholesky_one_step_tail_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A : NLA.RA02.Square n) (hA : A.PosSemidef) :
    (∑ p, NLA.RA02.pivotMass A p * NLA.RA02.rankTail (NLA.RA02.choleskyStep A p)
      (NLA.RA02.choleskyStep_posSemidef A hA p).isHermitian (k-1)) ≤
      2*NLA.RA02.rankTail A hA.isHermitian k := by
  by_cases hne : A = 0
  · subst A
    have hz : ∀ (hH : (0 : NLA.RA02.Square n).IsHermitian) (r : ℕ), NLA.RA02.rankTail 0 hH r = 0 := by
      intro hH r
      exact rankTail_zero_matrix hA r
    simp only [NLA.RA02.choleskyStep_zero, hz, mul_zero, Finset.sum_const_zero, le_refl]
  · obtain ⟨V, hV⟩ := exists_ordered_eigenbasis A hA.isHermitian
    have hb := Finset.sum_le_sum (fun p (_ : p ∈ (Finset.univ : Finset (Fin n))) =>
      cholesky_pivot_tail_bound hk hkn A hA hne V hV p)
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, NLA.RA02.sum_pivotMass n (by omega) A,
      one_mul, sum_pivot_tail_weights] at hb
    change _ ≤ NLA.RA02.rankTail A hA.isHermitian k + NLA.RA02.rankTail A hA.isHermitian k at hb
    linarith

#print axioms cholesky_one_step_tail_bound
#print axioms cholesky_pivot_tail_bound
end NLA.RA02.Paper
