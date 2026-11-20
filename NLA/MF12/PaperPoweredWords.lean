module

public import NLA.MF12.Lower

@[expose] public section

/- Replacing the contracting generator by a positive integer power preserves
the fractional polynomial exponent. This word-level part supplies the upper
bound; the lower bound needs gaps at multiples of the powering exponent. -/
set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

def expandPoweredWord (k : ℕ) (w : List Bool) : List Bool :=
  w.flatMap (fun b => if b then [true] else List.replicate k false)

theorem expanded_product {d : ℕ} (A P : Square d) (k : ℕ) (w : List Bool) :
    binaryProduct (A^k) P w = binaryProduct A P (expandPoweredWord k w) := by
  induction w with
  | nil => simp [expandPoweredWord]
  | cons b w ih =>
    simp only [expandPoweredWord] at ih
    cases b <;> simp [expandPoweredWord, List.flatMap_cons, binaryProduct_cons,
      binaryProduct_append, ih]

theorem expanded_length (k : ℕ) (hk : 1 ≤ k) (w : List Bool) :
    w.length ≤ (expandPoweredWord k w).length ∧
      (expandPoweredWord k w).length ≤ k*w.length := by
  induction w with
  | nil => simp [expandPoweredWord]
  | cons b w ih =>
    cases b <;> simp only [expandPoweredWord, List.flatMap_cons, Bool.false_eq_true,
      ↓reduceIte, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil, Nat.add_zero, Nat.mul_add, Nat.mul_one] at * <;> constructor <;> omega

theorem powered_all_word_upper (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (k : ℕ) (hk : 1 ≤ k) (w : List Bool) (hw : 1 ≤ w.length) :
    spectralNorm (binaryProduct ((fractionalMatrix α)^k) resetMatrix w) ≤
      (fractionalUpper α * Real.rpow (k : ℝ) α) * Real.rpow (w.length : ℝ) α := by
  have hl := expanded_length k hk w
  have hu := fractional_all_word_upper α hα hα1 (expandPoweredWord k w) (hw.trans hl.1)
  rw [expanded_product]
  have hc : 0 ≤ fractionalUpper α := by unfold fractionalUpper; positivity
  calc
    _ ≤ fractionalUpper α * Real.rpow ((expandPoweredWord k w).length : ℝ) α := hu
    _ ≤ fractionalUpper α * Real.rpow ((k*w.length : ℕ) : ℝ) α :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hl.2) hα.le) hc
    _ = _ := by
      simp only [Nat.cast_mul, Real.rpow_eq_pow]
      rw [Real.mul_rpow (show (0 : ℝ) ≤ k by positivity)
        (show (0 : ℝ) ≤ w.length by positivity)]
      ring

#print axioms expanded_product
#print axioms powered_all_word_upper
end NLA.MF12.Paper
