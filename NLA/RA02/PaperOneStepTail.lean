module

public import NLA.RA02.PaperTailFrame
public import NLA.RA02.PaperDiagonalBounds

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem sum_tailIndex {n k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    (∑ j : Fin (n-k), f (tailIndex k hk j)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), f i := by
  apply Finset.sum_bij (fun j _ => tailIndex k hk j)
  · intro j _
    simp [tailIndex]
  · intro i _ j _ he
    exact tailIndex_injective hk he
  · intro i hi
    have hki := (Finset.mem_filter.mp hi).2
    refine ⟨⟨i.val-k, by omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp [tailIndex, Nat.add_sub_of_le hki]
  · intro j _
    rfl

theorem rotated_tail_bound {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (R : NLA.RA02.Square n) (hR : R.PosSemidef) (V : Matrix.unitaryGroup (Fin n) ℂ)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (v : Fin n → ℂ) (b c : ℝ)
    (hb : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i*Complex.normSq (v i) = b)
    (hc : 0 ≤ c) (hd : 0 < b+c)
    (hrot : (V : NLA.RA02.Square n).conjTranspose*R*(V : NLA.RA02.Square n) =
      diagonalPivotUpdate a v (b+c)) :
    (b+c)*NLA.RA02.rankTail R hR.isHermitian (k-1) ≤
      (b+c)*(∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), a i) + (∑ i, a i)*c := by
  obtain ⟨g, hg, hn, hbnd⟩ := diagonalPivotUpdate_exists_probe hk hkn a ha v b c hb hc hd
  have ht := rankTail_le_headTail_probe hkn hk R hR V g hg hn
  rw [hrot, Complex.add_re] at ht
  rw [Complex.re_sum] at ht
  have hsum : (∑ j : Fin (n-k), (diagonalPivotUpdate a v (b+c) (tailIndex k hkn j) (tailIndex k hkn j)).re) ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), a i := by
    rw [← sum_tailIndex hkn]
    exact Finset.sum_le_sum (fun j _ => diagonalPivotUpdate_diag_le a v (b+c) hd.le _)
  have hm := mul_le_mul_of_nonneg_left ht hd.le
  have hm' := mul_le_mul_of_nonneg_left hsum hd.le
  nlinarith

#print axioms rotated_tail_bound
end NLA.RA02.Paper
