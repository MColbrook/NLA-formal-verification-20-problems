module

public import NLA.MD06.GraphCriticalityHessian.Structural
public import NLA.MD06.GraphCriticalityHessian.OrderedPairs
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix

@[expose] public section
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reference.MD06Actual
open Matrix
open scoped BigOperators

theorem adjacent_square_double_sum {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then (z i-z j)^2 else 0) = 2 * LaplacianQuadratic G z := by
  classical
  let f : Fin n → Fin n → ℝ := fun i j => if G.Adj i j then (z i-z j)^2 else 0
  have hd : ∀ i, f i i = 0 := by intro i; simp [f]
  change (∑ i, ∑ j, f i j) = _
  rw [sum_ordered_pairs f hd]
  unfold LaplacianQuadratic
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    by_cases hG : G.Adj i j
    · have hrev : G.Adj j i := G.adj_symm hG
      simp only [f,if_pos hG,if_pos hrev,hij,true_and]
      ring
    · have hrev : ¬ G.Adj j i := fun h => hG (G.adj_symm h)
      simp [f,hG,hrev,hij]
  · have he : ¬ (i < j ∧ G.Adj i j) := fun h => hij h.1
    simp only [if_neg hij,if_neg he,mul_zero]

theorem actual_laplacian_quadratic_identity {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n → ℝ) :
    z ⬝ᵥ (G.lapMatrix ℝ) *ᵥ z = LaplacianQuadratic G z := by
  rw [← Matrix.toLinearMap₂'_apply',G.lapMatrix_toLinearMap₂' (R := ℝ) z,adjacent_square_double_sum]
  ring

theorem hessian_lower_bound_actual_laplacian {n : ℕ} (G : SimpleGraph (Fin n))
    (theta : Phase n) (z : Fin n → ℝ) (c : ℝ)
    (h : ∀ i j, G.Adj i j → c ≤ Real.Angle.cos (theta i-theta j)) :
    c * (z ⬝ᵥ (G.lapMatrix ℝ) *ᵥ z) ≤ HessianQuadratic G theta z := by
  rw [actual_laplacian_quadratic_identity]
  exact hessian_lower_bound_from_actual_edge_cosines G theta z c h

#print axioms adjacent_square_double_sum
#print axioms actual_laplacian_quadratic_identity
#print axioms hessian_lower_bound_actual_laplacian
end Reference.MD06Actual
