module

public import NLA.RA02.PaperSurvivalEncoding

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem historyIndicator_eq_ite {r : ℕ} (h : Fin r ↪ Fin (r+1)) :
    historyIndicator h = if SurvivingHistory h then 1 else 0 := by
  by_cases hs : SurvivingHistory h
  · rw [if_pos hs]
    apply Finset.prod_eq_one
    intro s _
    exact if_pos (hs s)
  · rw [if_neg hs]
    obtain ⟨s,hbad⟩ := not_forall.mp hs
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    exact if_neg hbad

theorem retainedEmbedding_injective (r : ℕ) : Function.Injective (retainedEmbedding r) := by
  intro a b hab
  apply NLA.RA02.retainedHistory_injective r
  funext i
  exact congrArg (fun h : Fin r ↪ Fin (r+1) => h i) hab

theorem history_indicator_sum (r : ℕ) :
    (∑ h : Fin r ↪ Fin (r+1), historyIndicator h) = (2 : ℝ)^r := by
  have he : (∑ bits : Fin r → Bool, historyIndicator (retainedEmbedding r bits)) =
      ∑ h : Fin r ↪ Fin (r+1), historyIndicator h := by
    apply Fintype.sum_of_injective (retainedEmbedding r) (retainedEmbedding_injective r)
    · intro h hn
      rw [historyIndicator_eq_ite, if_neg]
      intro hs
      exact hn (surviving_is_retained h hs)
    · intro bits
      rfl
  rw [← he]
  have hone : ∀ bits : Fin r → Bool, historyIndicator (retainedEmbedding r bits) = 1 := by
    intro bits
    rw [historyIndicator_eq_ite, if_pos (retainedEmbedding_survives r bits)]
  simp_rw [hone]
  simp

theorem history_pair_indicator_sum (r : ℕ) :
    (∑ rows : Fin r ↪ Fin (r+1), ∑ cols : Fin r ↪ Fin (r+1),
      historyIndicator rows * historyIndicator cols) = (4 : ℝ)^r := by
  rw [← Finset.sum_mul_sum, history_indicator_sum, ← mul_pow]
  norm_num

#print axioms history_pair_indicator_sum
end NLA.RA02.Paper
