module

public import NLA.TR04.AllOrderSharp.Definitions
public import NLA.TR04.AllOrderSharp.Projection

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp

theorem weighted_selector_gram {N q : ℕ} (hN : q+2 ≤ N)
    (c : Fin (q+2) → ℝ) :
    family hN (Matrix.diagonal c) * (family hN (Matrix.diagonal c)).transpose =
      Matrix.diagonal (fun i => c i ^ 2) := by
  rw [family_gram, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

theorem weighted_selector_row_gram {N q : ℕ} (hN : q+2 ≤ N)
    (c : Fin (q+2) → ℝ) (i j : Fin (q+2)) :
    (∑ b, family hN (Matrix.diagonal c) i b * family hN (Matrix.diagonal c) j b) =
      if i = j then c i ^ 2 else 0 := by
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
    using congrArg (fun A => A i j) (weighted_selector_gram hN c)

theorem family_weighted_embedding {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (c : Fin (q+2) → ℝ) :
    family hN (V * Matrix.diagonal c) = V * family hN (Matrix.diagonal c) := by
  exact Matrix.mul_assoc _ _ _

theorem weighted_selector_drop_row {N q : ℕ} (hN : q+2 ≤ N)
    (c : Fin (q+2) → ℝ) (i₀ : Fin (q+2)) :
    (fun i j => if i = i₀ then 0 else family hN (Matrix.diagonal c) i j) =
      family hN (Matrix.diagonal (fun i => if i = i₀ then 0 else c i)) := by
  rw [drop_row_eq_diagonal]
  unfold family
  rw [← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  by_cases hi : i = i₀ <;> simp [keepMask, hi]

theorem family_single_row_error {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (hV : V.transpose * V = 1)
    (c : Fin (q+2) → ℝ) (i₀ : Fin (q+2)) :
    Reference.TensorGrouping.entryFrobeniusSq
      (family hN (V * Matrix.diagonal c) -
        family hN (V * Matrix.diagonal (fun i => if i = i₀ then 0 else c i))) = c i₀ ^ 2 := by
  rw [family_weighted_embedding, family_weighted_embedding, ← Matrix.mul_sub,
    Reference.TensorGrouping.finite_column_lifting_frobenius_eq V hV]
  have hdrop : ∀ i j,
      family hN (Matrix.diagonal (fun b => if b = i₀ then 0 else c b)) i j =
        if i = i₀ then 0 else family hN (Matrix.diagonal c) i j := by
    intro i j
    by_cases hi : i = i₀ <;> simp [family, Matrix.diagonal_mul, hi]
  change (∑ i, ∑ j, (family hN (Matrix.diagonal c) i j -
    family hN (Matrix.diagonal (fun b => if b = i₀ then 0 else c b)) i j) ^ 2) = c i₀ ^ 2
  simp only [hdrop]
  rw [Finset.sum_eq_single i₀]
  · simpa [pow_two] using
      weighted_selector_row_gram hN c i₀ i₀
  · intro i _ hi
    simp [hi]
  · simp

#print axioms weighted_selector_gram
#print axioms family_weighted_embedding

end NLA.TR04.AllOrderSharp
