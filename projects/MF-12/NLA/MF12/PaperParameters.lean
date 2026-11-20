module

public import NLA.MF12.PaperDefinitions
public import NLA.MF12.Parameters

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

theorem parameter_loss_bounds (lam : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (q : ℕ) (hq : 1 ≤ q) :
    0 < parameterLoss lam q ∧ parameterLoss lam q ≤ 1/4 := by
  refine ⟨mul_pos (by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)) (pow_pos hlam q), ?_⟩
  have hp : lam^q ≤ baseLambda^q := pow_le_pow_left₀ hlam.le hlamq q
  exact (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg q)).trans (loss_le_quarter q)

theorem parameter_gain_identity (lam α : ℝ) (hlam : 0 < lam)
    (hα : 0 < α) (hα1 : α < 1) (q : ℕ) :
    parameterGain (Real.rpow lam (1-α)) q =
      Real.rpow (q : ℝ) α * Real.rpow (parameterLoss lam q) (1-α) := by
  have hqpow : (q : ℝ)^α * (q : ℝ)^(1-α) = q := by
    rw [← Real.rpow_add_of_nonneg (Nat.cast_nonneg q) hα.le (sub_nonneg.mpr hα1.le)]
    simp
  calc
    parameterGain (Real.rpow lam (1-α)) q = (q : ℝ) * Real.rpow (lam^q) (1-α) := by
      dsimp only [parameterGain]
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_pow_comm hlam.le]
    _ = Real.rpow (q : ℝ) α * Real.rpow (parameterLoss lam q) (1-α) := by
      simp only [parameterLoss, Real.rpow_eq_pow]
      rw [Real.mul_rpow (Nat.cast_nonneg q) (pow_nonneg hlam.le q)]
      rw [← mul_assoc, hqpow]

#print axioms parameter_loss_bounds
#print axioms parameter_gain_identity
end NLA.MF12.Paper
