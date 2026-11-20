module

public import NLA.MD06.GraphCriticalityHessian.Structural
public import NLA.MD06.GraphCriticalityHessian.OrderedPairs

@[expose] public section
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reference.MD06Actual
open scoped BigOperators

theorem gradient_pairing_upper_edges {n : ℕ} (G : SimpleGraph (Fin n))
    (theta : Phase n) (z : Fin n → ℝ) :
    (∑ i, z i * Gradient G theta i) = ∑ i, ∑ j,
      if i < j ∧ G.Adj i j then Real.Angle.sin (theta i-theta j) * (z i-z j) else 0 := by
  classical
  let f : Fin n → Fin n → ℝ := fun i j => if G.Adj i j then z i * Real.Angle.sin (theta i-theta j) else 0
  have hdiag : ∀ i, f i i = 0 := by intro i; simp [f]
  have hs : (∑ i, z i * Gradient G theta i) = ∑ i, ∑ j, f i j := by
    simp only [Gradient,Finset.mul_sum,mul_ite,mul_zero,f]
  rw [hs,sum_ordered_pairs f hdiag]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [if_pos hij]
    by_cases hG : G.Adj i j
    · have hrev : G.Adj j i := G.adj_symm hG
      have hsub : theta j-theta i = -(theta i-theta j) := by abel
      simp only [f,if_pos hG,if_pos hrev,hij,true_and,hsub,Real.Angle.sin_neg]
      ring
    · have hrev : ¬ G.Adj j i := fun hh => hG (G.adj_symm hh)
      simp [f,hG,hrev,hij]
  · have he : ¬ (i < j ∧ G.Adj i j) := fun h => hij h.1
    simp only [if_neg hij,if_neg he]

theorem line_force_zero_gradient_pairing {n : ℕ} (G : SimpleGraph (Fin n))
    (phi z : Fin n → ℝ) :
    LineForce G phi z 0 = ∑ i, z i * Gradient G (fun i => (phi i : Real.Angle)) i := by
  rw [gradient_pairing_upper_edges]
  simp only [LineForce,zero_mul,add_zero,← Real.Angle.coe_sub,Real.Angle.sin_coe]

theorem actual_critical_iff_all_line_forces_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (phi : Fin n → ℝ) :
    (∀ i, Gradient G (fun i => (phi i : Real.Angle)) i = 0) ↔
      ∀ z : Fin n → ℝ, LineForce G phi z 0 = 0 := by
  classical
  constructor
  · intro h z
    rw [line_force_zero_gradient_pairing]
    simp only [h,mul_zero,Finset.sum_const_zero]
  · intro h i
    have hi := h (Pi.single i (1 : ℝ))
    rw [line_force_zero_gradient_pairing] at hi
    simpa [Pi.single_apply] using hi

#print axioms gradient_pairing_upper_edges
#print axioms line_force_zero_gradient_pairing
#print axioms actual_critical_iff_all_line_forces_zero
end Reference.MD06Actual
