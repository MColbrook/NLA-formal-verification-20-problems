module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Equality refinement of the checked RA02 scalar weighted-tail argument.
CETW25 Section 5.4 / Gilles--Wilber Appendix A.1 attribution retained.
New reference-only equality formalization by Codex, 2026-10-03. -/
public import NLA.TR04.RealSVD.RealWeights

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace Reference.RealOptimalityEquality

theorem weighted_tail_equality_zero_above {ι : Type*} [Fintype ι]
    (S : Finset ι) (a w : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1)
    (hbelow : ∀ i ∈ S, a i ≤ c) (habove : ∀ i ∉ S, c ≤ a i)
    (hmass : (S.card : ℝ) ≤ ∑ i, w i)
    (he : (∑ i, a i * w i) = ∑ i ∈ S, a i) :
    ∀ i, c < a i → w i = 0 := by
  classical
  let delta : ι → ℝ := fun i => a i * w i - (if i ∈ S then a i else 0) -
    c * (w i - if i ∈ S then 1 else 0)
  have hd : ∀ i, 0 ≤ delta i := by
    intro i
    by_cases hi : i ∈ S
    · simp only [delta, if_pos hi]
      have hm := mul_nonneg (sub_nonneg.mpr (hbelow i hi))
        (sub_nonneg.mpr (hw i).2)
      nlinarith
    · simp only [delta, if_neg hi, sub_zero]
      have hm := mul_nonneg (sub_nonneg.mpr (habove i hi)) (hw i).1
      nlinarith
  have ha : (∑ i, if i ∈ S then a i else 0) = ∑ i ∈ S, a i := by simp
  have hcard : (∑ i, if i ∈ S then (1 : ℝ) else 0) = (S.card : ℝ) := by simp
  have hs : (∑ i, delta i) = -c * ((∑ i, w i) - (S.card : ℝ)) := by
    dsimp [delta]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, he, ha, hcard]
    ring
  have hsum : (∑ i, delta i) ≤ 0 := by
    rw [hs]
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hc (sub_nonneg.mpr hmass))
  intro i hi
  have hinot : i ∉ S := by
    intro himem
    exact (not_lt_of_ge (hbelow i himem)) hi
  have hdi : delta i ≤ 0 :=
    (Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)).trans hsum
  simp only [delta, if_neg hinot, sub_zero] at hdi
  apply le_antisymm _ (hw i).1
  by_contra hwi
  have hp := mul_pos (sub_pos.mpr hi) (lt_of_not_ge hwi)
  nlinarith

#print axioms weighted_tail_equality_zero_above
end Reference.RealOptimalityEquality

