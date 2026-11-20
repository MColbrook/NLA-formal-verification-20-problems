module

public import NLA.TR04.FixedSharp.EqualityHelpers

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp

variable {n : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The squared norm of a combination of orthogonal rows. -/
theorem orthogonal_rows_energy (A : Matrix (Fin n) κ ℝ) (w : Fin n → ℝ)
    (hgram : ∀ i k, (∑ j, A i j * A k j) = if i = k then w i else 0)
    (v : Fin n → ℝ) :
    (∑ j, (∑ i, A i j * v i) ^ 2) = ∑ i, w i * v i ^ 2 := by
  calc
    _ = ∑ j, ∑ i, ∑ k, (A i j * A k j) * (v i * v k) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ i, ∑ k, (∑ j, A i j * A k j) * (v i * v k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = _ := by simp [hgram, pow_two]

/-- Among matrices of rank below the number of orthogonal nonzero rows, a
strictly smallest row is the unique possible discarded row at its own error.
This statement applies to the actual matrix approximation, not just its energy.
-/
theorem smallest_row_unique (A X : Matrix (Fin n) κ ℝ) (w : Fin n → ℝ)
    (hgram : ∀ i k, (∑ j, A i j * A k j) = if i = k then w i else 0)
    (i₀ : Fin n) (hsmall : ∀ i, i ≠ i₀ → w i₀ < w i)
    (hrank : X.rank < n)
    (herror : (∑ i, ∑ j, (A i j - X i j) ^ 2) ≤ w i₀) :
    X = fun i j => if i = i₀ then 0 else A i j := by
  classical
  obtain ⟨v, hv, hker⟩ := NLA.TR04.FixedSharp.exists_unit_kernel X.transpose
    (by rw [Matrix.rank_transpose]; exact hrank)
  have hb := NLA.TR04.FixedSharp.kernel_action_le_error A.transpose X.transpose v hv hker
  rw [Finset.sum_comm] at hb
  have he : (∑ i, w i * v i ^ 2) ≤ w i₀ := by
    rw [← orthogonal_rows_energy A w hgram v]
    exact hb.trans herror
  have hnonneg : ∀ i, 0 ≤ (w i - w i₀) * v i ^ 2 := by
    intro i
    by_cases hi : i = i₀
    · subst i; simp
    · exact mul_nonneg (sub_nonneg.mpr (hsmall i hi).le) (sq_nonneg _)
  have hsum : (∑ i, (w i - w i₀) * v i ^ 2) ≤ 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hv, mul_one]
    linarith
  have hvzero : ∀ i, i ≠ i₀ → v i = 0 := by
    intro i hi
    have hterm : (w i - w i₀) * v i ^ 2 ≤ 0 :=
      (Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ i)).trans hsum
    have hsq : v i ^ 2 = 0 := by
      by_contra hne
      have hpos := mul_pos (sub_pos.mpr (hsmall i hi))
        (lt_of_le_of_ne (sq_nonneg (v i)) (Ne.symm hne))
      linarith
    nlinarith
  have hvmin : v i₀ ≠ 0 := by
    intro hz
    have hall : ∀ i, v i = 0 := by
      intro i
      by_cases hi : i = i₀
      · simpa [hi] using hz
      · exact hvzero i hi
    simp only [hall, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at hv
    norm_num at hv
  have hrow : ∀ j, X i₀ j = 0 := by
    intro j
    have hk : X i₀ j * v i₀ = 0 := by
      have hh := hker j
      change (∑ i, X i j * v i) = 0 at hh
      rw [Finset.sum_eq_single i₀] at hh
      · exact hh
      · intro i _ hi
        rw [hvzero i hi, mul_zero]
      · simp
    exact (mul_eq_zero.mp hk).resolve_right hvmin
  have hrowerror : (∑ j, (A i₀ j - X i₀ j) ^ 2) = w i₀ := by
    simp only [hrow, sub_zero, pow_two]
    simpa using hgram i₀ i₀
  have hsame := NLA.TR04.FixedSharp.row_exhausts_error A X i₀
    (by rw [hrowerror]; exact herror)
  ext i j
  by_cases hi : i = i₀
  · subst i; simp [hrow]
  · simp only [hi, if_false]
    exact hsame i hi j

#print axioms orthogonal_rows_energy
#print axioms smallest_row_unique

end NLA.TR04.AllOrderSharp
