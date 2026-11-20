module

public import NLA.MD06.GraphCriticalityHessian.LineDerivatives

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Actual
open scoped BigOperators

theorem energy_rotation_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (theta : Phase n) (a : Real.Angle) :
    Energy G (fun i => theta i+a) = Energy G theta := by
  simp only [Energy,add_sub_add_right_eq_sub]

theorem gradient_rotation_invariant {n : ℕ} (G : SimpleGraph (Fin n)) (theta : Phase n) (a : Real.Angle) :
    Gradient G (fun i => theta i+a) = Gradient G theta := by
  funext i
  simp only [Gradient,add_sub_add_right_eq_sub]

theorem gradient_sum_zero {n : ℕ} (G : SimpleGraph (Fin n)) (theta : Phase n) :
    (∑ i, Gradient G theta i) = 0 := by
  classical
  let term : Fin n → Fin n → ℝ := fun i j => if G.Adj i j then Real.Angle.sin (theta i-theta j) else 0
  have hab : ∀ i j, term i j = -term j i := by
    intro i j
    have hsub : theta i-theta j = -(theta j-theta i) := by abel
    by_cases he : G.Adj i j
    · have hf : G.Adj j i := G.adj_symm he
      simp only [term,if_pos he,if_pos hf,hsub,Real.Angle.sin_neg]
    · have hf : ¬ G.Adj j i := fun hh => he (G.adj_symm hh)
      simp only [term,if_neg he,if_neg hf,neg_zero]
  have hs : (∑ i, ∑ j, term i j) = -(∑ i, ∑ j, term i j) := by
    calc
      (∑ i, ∑ j, term i j) = ∑ i, ∑ j, -term j i := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_congr rfl (fun j _ => hab i j)
      _ = -(∑ i, ∑ j, term j i) := by simp only [Finset.sum_neg_distrib]
      _ = -(∑ i, ∑ j, term i j) := by rw [Finset.sum_comm]
  change (∑ i, ∑ j, term i j) = 0
  linarith

theorem synchronized_gradient_zero {n : ℕ} (G : SimpleGraph (Fin n)) (theta : Phase n)
    (h : Synchronized theta) (i : Fin n) : Gradient G theta i = 0 := by
  classical
  unfold Gradient
  apply Finset.sum_eq_zero
  intro j _
  simp only [h i j,sub_self,Real.Angle.sin_zero,ite_self]

theorem synchronized_hessian_laplacian {n : ℕ} (G : SimpleGraph (Fin n)) (theta : Phase n)
    (h : Synchronized theta) (z : Fin n → ℝ) : HessianQuadratic G theta z = LaplacianQuadratic G z := by
  classical
  unfold HessianQuadratic LaplacianQuadratic
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [h i j,sub_self,Real.Angle.cos_zero,one_mul]

theorem hessian_lower_bound_from_actual_edge_cosines {n : ℕ} (G : SimpleGraph (Fin n))
    (theta : Phase n) (z : Fin n → ℝ) (c : ℝ)
    (h : ∀ i j, G.Adj i j → c ≤ Real.Angle.cos (theta i-theta j)) :
    c * LaplacianQuadratic G z ≤ HessianQuadratic G theta z := by
  classical
  unfold LaplacianQuadratic HessianQuadratic
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases he : i < j ∧ G.Adj i j
  · simp only [if_pos he]
    exact mul_le_mul_of_nonneg_right (h i j he.2) (sq_nonneg (z i-z j))
  · simp only [if_neg he,mul_zero,le_refl]

#print axioms energy_rotation_invariant
#print axioms gradient_rotation_invariant
#print axioms gradient_sum_zero
#print axioms synchronized_gradient_zero
#print axioms synchronized_hessian_laplacian
#print axioms hessian_lower_bound_from_actual_edge_cosines
end Reference.MD06Actual
