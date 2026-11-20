module

public import NLA.MF12.PaperAlgebra
public import NLA.MF12.PaperParameters
public import NLA.MF12.HolderBound

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace NLA.MF12.Paper

def diagonalBudget (lam : ℝ) (qs : List ℕ) : ℝ :=
  (qs.map (fun q => 1 - parameterLoss lam q)).prod
def tailWeight (lam : ℝ) (qs : List ℕ) (i : ℕ) : ℝ := diagonalBudget lam (qs.drop (i+1))
def offBudget (lam α : ℝ) (qs : List ℕ) : ℝ :=
  ∑ i ∈ Finset.range qs.length,
    parameterGain (Real.rpow lam (1-α)) (qs.getD i 0) * tailWeight lam qs i

theorem loss_nonneg (lam : ℝ) (hlam : 0 < lam) (q : ℕ) : 0 ≤ parameterLoss lam q :=
  mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hlam.le _)

theorem loss_le_one (lam : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4) (q : ℕ) :
    parameterLoss lam q ≤ 1 := by
  by_cases hq : q = 0
  · simp [hq, parameterLoss]
  · exact ((parameter_loss_bounds lam hlam hlamq q (Nat.one_le_iff_ne_zero.mpr hq)).2).trans
      (by norm_num)

theorem diagonal_bounds (lam : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4) (qs : List ℕ) :
    0 ≤ diagonalBudget lam qs ∧ diagonalBudget lam qs ≤ 1 := by
  induction qs with
  | nil => norm_num [diagonalBudget]
  | cons q qs ih =>
      change 0 ≤ (1-parameterLoss lam q)*diagonalBudget lam qs ∧
        (1-parameterLoss lam q)*diagonalBudget lam qs ≤ 1
      have ha := sub_nonneg.mpr (loss_le_one lam hlam hlamq q)
      refine ⟨mul_nonneg ha ih.1, ?_⟩
      have hu := mul_le_mul_of_nonneg_left ih.2 ha
      have hl := loss_nonneg lam hlam q
      nlinarith

theorem tail_bounds (lam : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4) (qs : List ℕ) (i : ℕ) :
    0 ≤ tailWeight lam qs i ∧ tailWeight lam qs i ≤ 1 :=
  diagonal_bounds lam hlam hlamq _

theorem loss_budget (lam : ℝ) (qs : List ℕ) :
    (∑ i ∈ Finset.range qs.length, parameterLoss lam (qs.getD i 0) * tailWeight lam qs i) =
      1 - diagonalBudget lam qs := by
  induction qs with
  | nil => simp [diagonalBudget]
  | cons q qs ih =>
      rw [List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      change (∑ i ∈ Finset.range qs.length, parameterLoss lam (qs.getD i 0) * tailWeight lam qs i) +
        parameterLoss lam q * diagonalBudget lam qs = 1 - (1-parameterLoss lam q)*diagonalBudget lam qs
      rw [ih]
      ring

theorem off_cons (lam α : ℝ) (q : ℕ) (qs : List ℕ) :
    offBudget lam α (q::qs) = offBudget lam α qs +
      parameterGain (Real.rpow lam (1-α)) q * diagonalBudget lam qs := by
  unfold offBudget
  rw [List.length_cons, Finset.sum_range_succ']
  rfl

theorem product_formula (lam α : ℝ) (qs : List ℕ) :
    matrixProduct (qs.map (parameterCompressed lam (Real.rpow lam (1-α)))) =
      !![diagonalBudget lam qs, offBudget lam α qs; 0,1] := by
  induction qs with
  | nil =>
      simp only [List.map_nil, matrixProduct_nil]
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [diagonalBudget, offBudget, Matrix.one_apply]
  | cons q qs ih =>
      rw [List.map_cons, matrixProduct_cons, ih, parameter_compressed_powers, off_cons]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, diagonalBudget] <;> ring

theorem weighted_gain (lam α : ℝ) (hlam : 0 < lam) (hα : 0 < α) (hα1 : α < 1)
    (q : ℕ) (w : ℝ) (hw : 0 ≤ w) :
    parameterGain (Real.rpow lam (1-α)) q * w =
      Real.rpow ((q : ℝ)*w) α * Real.rpow (parameterLoss lam q*w) (1-α) := by
  have hg := parameter_gain_identity lam α hlam hα hα1 q
  have hwp : w^α * w^(1-α) = w := by
    rw [← Real.rpow_add_of_nonneg hw hα.le (sub_nonneg.mpr hα1.le)]
    simp
  simp only [Real.rpow_eq_pow] at hg ⊢
  rw [Real.mul_rpow (Nat.cast_nonneg q) hw,
    Real.mul_rpow (loss_nonneg lam hlam q) hw]
  calc
    parameterGain (lam^(1-α)) q * w =
        ((q : ℝ)^α * parameterLoss lam q^(1-α)) * (w^α * w^(1-α)) := by rw [hwp, hg]
    _ = ((q : ℝ)^α * w^α) * (parameterLoss lam q^(1-α) * w^(1-α)) := by ring

theorem off_bounds (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) (qs : List ℕ) :
    0 ≤ offBudget lam α qs ∧ offBudget lam α qs ≤ Real.rpow (qs.sum : ℝ) α := by
  constructor
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (Real.rpow_nonneg hlam.le _) _)) (tail_bounds lam hlam hlamq qs i).1
  · let f : ℕ → ℝ := fun i => (qs.getD i 0 : ℝ) * tailWeight lam qs i
    let g : ℕ → ℝ := fun i => parameterLoss lam (qs.getD i 0) * tailWeight lam qs i
    have hf (i : ℕ) : 0 ≤ f i := mul_nonneg (Nat.cast_nonneg _) (tail_bounds lam hlam hlamq qs i).1
    have hg (i : ℕ) : 0 ≤ g i := mul_nonneg (loss_nonneg lam hlam _) (tail_bounds lam hlam hlamq qs i).1
    have hF : (∑ i ∈ Finset.range qs.length, f i) ≤ (qs.sum : ℝ) := by
      rw [← sum_gap_values qs]
      apply Finset.sum_le_sum
      intro i _
      exact (mul_le_mul_of_nonneg_left (tail_bounds lam hlam hlamq qs i).2
        (Nat.cast_nonneg (qs.getD i 0))).trans_eq (mul_one _)
    have hG : (∑ i ∈ Finset.range qs.length, g i) ≤ 1 := by
      change (∑ i ∈ Finset.range qs.length, parameterLoss lam (qs.getD i 0) * tailWeight lam qs i) ≤ 1
      rw [loss_budget]
      have h := (diagonal_bounds lam hlam hlamq qs).1
      linarith
    have hF0 := Finset.sum_nonneg (s := Finset.range qs.length) (fun i _ => hf i)
    have hG0 := Finset.sum_nonneg (s := Finset.range qs.length) (fun i _ => hg i)
    calc
      offBudget lam α qs = ∑ i ∈ Finset.range qs.length, Real.rpow (f i) α * Real.rpow (g i) (1-α) := by
        apply Finset.sum_congr rfl
        intro i _
        exact weighted_gain lam α hlam hα hα1 _ _ (tail_bounds lam hlam hlamq qs i).1
      _ ≤ Real.rpow (∑ i ∈ Finset.range qs.length, f i) α *
          Real.rpow (∑ i ∈ Finset.range qs.length, g i) (1-α) :=
        fractional_holder _ f g hf hg α hα hα1
      _ ≤ Real.rpow (qs.sum : ℝ) α * 1 :=
        mul_le_mul (Real.rpow_le_rpow hF0 hF hα.le)
          (Real.rpow_le_one hG0 hG (sub_nonneg.mpr hα1.le))
          (Real.rpow_nonneg hG0 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = Real.rpow (qs.sum : ℝ) α := mul_one _

#print axioms product_formula
#print axioms off_bounds
end NLA.MF12.Paper
