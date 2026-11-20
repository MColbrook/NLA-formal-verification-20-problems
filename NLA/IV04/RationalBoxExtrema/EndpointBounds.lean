module

public import NLA.IV04.RationalBoxExtrema.Interpolation

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace Reference.IV04RationalBoxExtrema

theorem realized_row_bounds {m n : ℕ}
    (L U : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (s : Fin n → Bool) (x : Fin n → ℝ) (hs : inOrthant s x)
    (hx : x ∈ solutions L U b) : rowBounds L U b s x := by
  obtain ⟨A,hA,hAx⟩ := hx
  intro i
  have heq : (∑ j, A i j*x j) = (b i : ℝ) := by
    exact congrFun hAx i
  rw [← heq]
  constructor
  · apply Finset.sum_le_sum
    intro j _
    have hb := hA i j
    have hsj := hs j
    cases hj : s j
    · simp only [hj,Bool.false_eq_true,↓reduceIte] at hsj
      simp only [lowerRow,hj,Bool.false_eq_true,↓reduceIte]
      exact mul_le_mul_of_nonpos_right hb.2 hsj
    · simp only [hj,↓reduceIte] at hsj
      simp only [lowerRow,hj,↓reduceIte]
      exact mul_le_mul_of_nonneg_right hb.1 hsj
  · apply Finset.sum_le_sum
    intro j _
    have hb := hA i j
    have hsj := hs j
    cases hj : s j
    · simp only [hj,Bool.false_eq_true,↓reduceIte] at hsj
      simp only [upperRow,hj,Bool.false_eq_true,↓reduceIte]
      exact mul_le_mul_of_nonpos_right hb.1 hsj
    · simp only [hj,↓reduceIte] at hsj
      simp only [upperRow,hj,↓reduceIte]
      exact mul_le_mul_of_nonneg_right hb.2 hsj

theorem solutions_iff_signed_rowBounds {m n : ℕ}
    (L U : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ)
    (hLU : ∀ i j, L i j ≤ U i j) (x : Fin n → ℝ) :
    x ∈ solutions L U b ↔ ∃ s : Fin n → Bool, inOrthant s x ∧ rowBounds L U b s x := by
  classical
  constructor
  · intro hx
    let s : Fin n → Bool := fun j => decide (0 ≤ x j)
    have hs : inOrthant s x := by
      intro j
      by_cases hj : 0 ≤ x j <;> simp [s,hj,le_of_not_ge]
    exact ⟨s,hs,realized_row_bounds L U b s x hs hx⟩
  · rintro ⟨s,_,h⟩
    exact rowwise_interpolation L U b hLU s x h

#print axioms realized_row_bounds
#print axioms solutions_iff_signed_rowBounds
end Reference.IV04RationalBoxExtrema
