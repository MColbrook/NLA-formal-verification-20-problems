module

public import NLA.MF12.PaperBudget
public import NLA.MF12.JordanBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix
namespace NLA.MF12.Paper

theorem paper_compressed_lemma (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) :
    (∀ q : ℕ, parameterCompressed lam (Real.rpow lam (1-α)) q =
      !![1-parameterLoss lam q, parameterGain (Real.rpow lam (1-α)) q; 0,1]) ∧
    parameterLoss lam 0 = 0 ∧ parameterGain (Real.rpow lam (1-α)) 0 = 0 ∧
    ∀ q : ℕ, 1 ≤ q → 0 < parameterLoss lam q ∧ parameterLoss lam q ≤ 1/4 ∧
      parameterGain (Real.rpow lam (1-α)) q =
        Real.rpow (q : ℝ) α * Real.rpow (parameterLoss lam q) (1-α) := by
  refine ⟨parameter_compressed_powers lam _, by simp [parameterLoss],
    by simp [parameterGain], ?_⟩
  intro q hq
  exact ⟨(parameter_loss_bounds lam hlam hlamq q hq).1,
    (parameter_loss_bounds lam hlam hlamq q hq).2,
    parameter_gain_identity lam α hlam hα hα1 q⟩

theorem paper_budget_lemma (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) (qs : List ℕ) :
    ∃ a z : ℝ,
      matrixProduct (qs.map (parameterCompressed lam (Real.rpow lam (1-α)))) =
        !![a,z; 0,1] ∧ 0 ≤ a ∧ a ≤ 1 ∧ 0 ≤ z ∧ z ≤ Real.rpow (qs.sum : ℝ) α := by
  exact ⟨diagonalBudget lam qs, offBudget lam α qs, product_formula lam α qs,
    (diagonal_bounds lam hlam hlamq qs).1, (diagonal_bounds lam hlam hlamq qs).2,
    (off_bounds lam α hlam hlamq hα hα1 qs).1,
    (off_bounds lam α hlam hlamq hα hα1 qs).2⟩

theorem paper_jordan_lemma (m : ℕ) :
    0 < (if m=0 then (1 : ℝ) else ((m : ℝ)^m)⁻¹) ∧
    ∀ n : ℕ, 1 ≤ n →
      (if m=0 then (1 : ℝ) else ((m : ℝ)^m)⁻¹) * (n : ℝ)^m ≤
        spectralNorm (jordanMatrix m ^ n) ∧
      spectralNorm (jordanMatrix m ^ n) ≤ ((m+1 : ℕ) : ℝ) * (n : ℝ)^m ∧
      (m=0 → spectralNorm (jordanMatrix m ^ n) = 1) := by
  refine ⟨jordanLower_pos m, ?_⟩
  intro n hn
  refine ⟨jordan_norm_lower m n, jordan_norm_upper m n hn, ?_⟩
  intro hm
  subst m
  have hl := jordan_power_norm_ge_one 0 n
  have hu := jordan_norm_upper 0 n hn
  norm_num at hu
  exact le_antisymm hu hl

#print axioms paper_compressed_lemma
#print axioms paper_budget_lemma
#print axioms paper_jordan_lemma

end NLA.MF12.Paper
