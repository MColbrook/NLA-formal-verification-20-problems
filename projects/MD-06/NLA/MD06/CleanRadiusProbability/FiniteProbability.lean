module

public import NLA.MD06.CleanRadiusProbability.Definitions
public import NLA.MD06.FiniteProbability.FiniteBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanRadiusProbability
open Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

theorem actual_regular_graph_probability_monotone (k : ℕ)
    (P Q : SimpleGraph (Fin (Size k)) → Prop)
    (h : ∀G,G.IsRegularOfDegree 3 → P G → Q G) :
    GraphProbability k P ≤ GraphProbability k Q := by
  simp only [actual_graph_probability_sample_formula]
  apply actual_counting_probability_monotone
  intro G hP
  exact h G.val G.property hP

theorem actual_bad_cycle_radius_probability_nonnegative (k ell R : ℕ) :
    0 ≤ GraphProbability k (fun G => BadCycleRadius G ell R) := by
  rw [actual_graph_probability_sample_formula]
  exact actual_counting_probability_nonnegative _

#print axioms actual_regular_graph_probability_monotone
#print axioms actual_bad_cycle_radius_probability_nonnegative
end Reference.MD06CleanRadiusProbability
