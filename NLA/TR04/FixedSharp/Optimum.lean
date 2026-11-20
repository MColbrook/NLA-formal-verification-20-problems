module

public import NLA.TR04.FixedSharp.KernelLower
public import NLA.TR04.FixedSharp.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace NLA.TR04.FixedSharp

@[simp] private theorem fin3_02 : (0 : Fin 3) ≠ 2 := by decide
@[simp] private theorem fin3_12 : (1 : Fin 3) ≠ 2 := by decide
@[simp] private theorem fin3_20 : (2 : Fin 3) ≠ 0 := by decide
@[simp] private theorem fin3_21 : (2 : Fin 3) ≠ 1 := by decide

theorem normSq_nonneg (A : Tensor) : 0 ≤ normSq A := by
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem normSq_secondCut (A : Tensor) :
    (∑ ij, ∑ k, secondCut A ij k ^ 2) = normSq A := by
  simp [secondCut, normSq, Fintype.sum_prod_type]

theorem actual_optimal_lower_bound (α β γ : ℝ) (hαγ : γ^2 ≤ α^2)
    (X : Tensor) (hX : feasible X) : γ^2 ≤ normSq (family α β γ - X) := by
  have hlow := gram_lower_le_rank_error (secondCut (family α β γ)) (secondCut X)
    (γ^2) (by have := hX.2; omega) (fun v => ?_)
  · simpa only [← normSq_secondCut, secondCut, Matrix.sub_apply] using hlow
  · simp only [secondCut, family, Fintype.sum_prod_type, Fin.sum_univ_succ,
      Fin.sum_univ_zero]
    norm_num [Fin.ext_iff]
    nlinarith [mul_nonneg (sub_nonneg.mpr hαγ) (sq_nonneg (v 0)),
      mul_nonneg (sq_nonneg β) (sq_nonneg (v 0))]

theorem optimalCandidate_feasible (α β : ℝ) : feasible (optimalCandidate α β) := by
  constructor
  · let U : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]
    let V : Matrix (Fin 2) (Fin 3 × Fin 2) ℝ := fun i jk =>
      if i = 0 ∧ jk = (0,0) then α else if i = 1 ∧ jk = (1,0) then β else 0
    have he : optimalCandidate α β = U * V := by
      ext i jk
      rcases jk with ⟨j,k⟩
      change optimalCandidate α β i (j,k) = ∑ l : Fin 2, U i l * V l (j,k)
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        norm_num [optimalCandidate, family, U, V, Matrix.mul_apply, Fin.sum_univ_succ]
    rw [he]
    exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)
  · let U : Matrix (Fin 3 × Fin 3) (Fin 1) ℝ := fun ij _ =>
      if ij = (0,0) then α else if ij = (1,1) then β else 0
    let V : Matrix (Fin 1) (Fin 2) ℝ := fun _ k => if k = 0 then 1 else 0
    have he : secondCut (optimalCandidate α β) = U * V := by
      ext ij k
      rcases ij with ⟨i,j⟩
      change secondCut (optimalCandidate α β) (i,j) k = ∑ l : Fin 1, U (i,j) l * V l k
      fin_cases i <;> fin_cases j <;> fin_cases k <;>
        norm_num [secondCut, optimalCandidate, family, U, V, Matrix.mul_apply, Fin.sum_univ_succ]
    rw [he]
    exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)

theorem optimalCandidate_error (α β γ : ℝ) :
    normSq (family α β γ - optimalCandidate α β) = γ^2 := by
  norm_num [normSq, family, optimalCandidate, Matrix.sub_apply, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

theorem actual_optimal_error (α β γ : ℝ) (hαγ : γ^2 ≤ α^2) :
    optimalError (family α β γ) = γ^2 := by
  let S := {z | ∃ X : Tensor, feasible X ∧ z = normSq (family α β γ - X)}
  have hb : BddBelow S := by
    refine ⟨γ^2, ?_⟩
    rintro z ⟨X,hX,rfl⟩
    exact actual_optimal_lower_bound α β γ hαγ X hX
  have hm : γ^2 ∈ S := ⟨optimalCandidate α β, optimalCandidate_feasible α β,
    (optimalCandidate_error α β γ).symm⟩
  apply le_antisymm
  · exact csInf_le hb hm
  · apply le_csInf ⟨_,hm⟩
    rintro z ⟨X,hX,rfl⟩
    exact actual_optimal_lower_bound α β γ hαγ X hX

theorem actual_greedy_candidate_error (α β γ : ℝ) :
    normSq (family α β γ - greedyCandidate α) = β^2 + γ^2 := by
  norm_num [normSq, family, greedyCandidate, Matrix.sub_apply, Fintype.sum_prod_type,
    Fin.sum_univ_succ]

#print axioms actual_optimal_error
#print axioms actual_greedy_candidate_error

end NLA.TR04.FixedSharp
