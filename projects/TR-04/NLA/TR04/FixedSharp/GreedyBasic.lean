module

public import NLA.TR04.FixedSharp.Optimum

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace NLA.TR04.FixedSharp

@[simp] private theorem fin3_02 : (0 : Fin 3) ≠ 2 := by decide
@[simp] private theorem fin3_12 : (1 : Fin 3) ≠ 2 := by decide
@[simp] private theorem fin3_20 : (2 : Fin 3) ≠ 0 := by decide
@[simp] private theorem fin3_21 : (2 : Fin 3) ≠ 1 := by decide

theorem firstCandidate_rank (α γ : ℝ) : (firstCandidate α γ).rank ≤ 2 := by
  let U : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 0; 0, 1]
  let V : Matrix (Fin 2) (Fin 3 × Fin 2) ℝ := fun i jk =>
    if i = 0 ∧ jk = (0,0) then α else if i = 1 ∧ jk = (2,1) then γ else 0
  have he : firstCandidate α γ = U * V := by
    ext i jk
    rcases jk with ⟨j,k⟩
    change firstCandidate α γ i (j,k) = ∑ l : Fin 2, U i l * V l (j,k)
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      norm_num [firstCandidate, family, U, V, Fin.sum_univ_succ]
  rw [he]
  exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)

theorem firstCandidate_error (α β γ : ℝ) :
    normSq (family α β γ - firstCandidate α γ) = β^2 := by
  norm_num [normSq, family, firstCandidate, Matrix.sub_apply, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

theorem actual_first_rank_lower (α β γ : ℝ)
    (hβα : β^2 ≤ α^2) (hβγ : β^2 ≤ γ^2)
    (X : Tensor) (hX : X.rank ≤ 2) : β^2 ≤ normSq (family α β γ - X) := by
  have hx : X.transpose.rank < 3 := by rw [Matrix.rank_transpose]; omega
  have hl := gram_lower_le_rank_error (family α β γ).transpose X.transpose (β^2) hx
    (fun v => ?_)
  · rw [Finset.sum_comm] at hl
    simpa only [Matrix.transpose_apply, normSq, Matrix.sub_apply] using hl
  · simp only [Matrix.transpose_apply, family, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Fin.sum_univ_zero]
    norm_num [Fin.ext_iff]
    nlinarith [mul_nonneg (sub_nonneg.mpr hβα) (sq_nonneg (v 0)),
      mul_nonneg (sub_nonneg.mpr hβγ) (sq_nonneg (v 2))]

theorem actual_first_best (α β γ : ℝ)
    (hβα : β^2 ≤ α^2) (hβγ : β^2 ≤ γ^2) :
    (firstCandidate α γ).rank ≤ 2 ∧
    ∀ X : Tensor, X.rank ≤ 2 →
      normSq (family α β γ - firstCandidate α γ) ≤ normSq (family α β γ - X) := by
  refine ⟨firstCandidate_rank α γ, ?_⟩
  intro X hX
  rw [firstCandidate_error]
  exact actual_first_rank_lower α β γ hβα hβγ X hX

theorem second_rank_lower (α β γ : ℝ) (hαγ : γ^2 ≤ α^2)
    (X : Tensor) (hX : (secondCut X).rank ≤ 1) :
    γ^2 ≤ normSq (family α β γ - X) := by
  have hl := gram_lower_le_rank_error (secondCut (family α β γ)) (secondCut X)
    (γ^2) (by omega) (fun v => ?_)
  · simpa only [← normSq_secondCut, secondCut, Matrix.sub_apply] using hl
  · simp only [secondCut, family, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.sum_univ_zero]
    norm_num [Fin.ext_iff]
    nlinarith [mul_nonneg (sub_nonneg.mpr hαγ) (sq_nonneg (v 0)),
      mul_nonneg (sq_nonneg β) (sq_nonneg (v 0))]

theorem greedyCandidate_feasible (α : ℝ) : feasible (greedyCandidate α) :=
  optimalCandidate_feasible α 0

theorem actual_second_best (α γ : ℝ) (hαγ : γ^2 ≤ α^2) :
    (secondCut (greedyCandidate α)).rank ≤ 1 ∧
    ∀ X : Tensor, (secondCut X).rank ≤ 1 →
      normSq (firstCandidate α γ - greedyCandidate α) ≤
        normSq (firstCandidate α γ - X) := by
  refine ⟨(greedyCandidate_feasible α).2, ?_⟩
  intro X hX
  have he : normSq (firstCandidate α γ - greedyCandidate α) = γ^2 := by
    simpa only [firstCandidate, zero_pow (by decide : 2 ≠ 0), zero_add] using
      actual_greedy_candidate_error α 0 γ
  rw [he]
  exact second_rank_lower α 0 γ hαγ X hX

#print axioms actual_first_best
#print axioms actual_second_best

end NLA.TR04.FixedSharp
