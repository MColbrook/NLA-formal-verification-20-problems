module

/- Actual affine-line exclusion in an arbitrary signed coordinate orthant. -/
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04ExactOutputSupport

 theorem nonnegative_affine_forall_direction_zero {x d : ℝ}
    (h : ∀ t : ℝ, 0 ≤ x+t*d) : d=0 := by
  by_contra hd
  have ht := h ((-x-1)/d)
  rw [div_mul_cancel₀ _ hd] at ht
  linarith

 theorem signed_orthant_affine_line_direction_zero {ι : Type*}
    (s x d : ι → ℝ) (hs : ∀ i, s i ≠ 0)
    (hline : ∀ t : ℝ, ∀ i, 0 ≤ s i*(x i+t*d i)) : d=0 := by
  funext i
  have hi : ∀ t : ℝ, 0 ≤ s i*x i+t*(s i*d i) := by
    intro t
    have h := hline t i
    nlinarith only [h]
  have hz := nonnegative_affine_forall_direction_zero hi
  exact (mul_eq_zero.mp hz).resolve_left (hs i)

#print axioms nonnegative_affine_forall_direction_zero
#print axioms signed_orthant_affine_line_direction_zero
end Reference.IV04ExactOutputSupport
