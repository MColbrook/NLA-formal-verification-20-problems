module

/- Supporting variational estimate for the Ky Fan arguments in Chen, Epperly,
Tropp and Webber, CPAM 2025, Lemma 5.5, and Gilles and Wilber, arXiv:2601.22344,
Theorem 3. New formalization with Codex assistance. -/
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem weighted_tail_bound {ι : Type*} [Fintype ι] (S : Finset ι)
    (a w : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hbelow : ∀ i ∈ S, a i ≤ c) (habove : ∀ i ∉ S, c ≤ a i)
    (hmass : (S.card : ℝ) ≤ ∑ i, w i) :
    ∑ i ∈ S, a i ≤ ∑ i, a i * w i := by
  have hp : ∀ i, (if i ∈ S then a i else 0) + c*(w i - if i ∈ S then 1 else 0) ≤ a i*w i := by
    intro i
    by_cases hi : i ∈ S
    · simp only [if_pos hi]
      have h := mul_nonneg (sub_nonneg.mpr (hbelow i hi)) (sub_nonneg.mpr (hw i).2)
      nlinarith
    · simp only [if_neg hi, sub_zero, zero_add]
      exact mul_le_mul_of_nonneg_right (habove i hi) (hw i).1
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hp i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hs
  have ha : (∑ i, if i ∈ S then a i else 0) = ∑ i ∈ S, a i := by simp
  have hcard : (∑ i, if i ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by simp
  rw [ha,hcard] at hs
  exact (le_add_of_nonneg_right (mul_nonneg hc (sub_nonneg.mpr hmass))).trans hs

theorem ordered_weighted_tail_bound {n : ℕ} (a w : Fin n → ℝ) (r : ℕ)
    (ha : Antitone a) (hpos : ∀ i, 0 ≤ a i)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hmass : ((Finset.univ.filter (fun i : Fin n => r ≤ i.val)).card : ℝ) ≤ ∑ i, w i) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ i.val), a i ≤ ∑ i, a i*w i := by
  by_cases hr : r < n
  · apply weighted_tail_bound _ a w (a ⟨r,hr⟩) (hpos _) hw
    · intro i hi
      exact ha (Fin.le_iff_val_le_val.mpr (Finset.mem_filter.mp hi).2)
    · intro i hi
      have hir : i.val < r := by simpa using hi
      exact ha (Fin.le_iff_val_le_val.mpr hir.le)
    · exact hmass
  · have hs : Finset.univ.filter (fun i : Fin n => r ≤ i.val) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hri := (Finset.mem_filter.mp hi).2
      omega
    rw [hs, Finset.sum_empty]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hpos i) (hw i).1)

#print axioms ordered_weighted_tail_bound
end NLA.RA02.Paper
