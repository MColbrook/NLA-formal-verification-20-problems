module

public import NLA.MD06.GraphExcessEncoding.PatternEncoding
public import NLA.MD06.BoundedExcessPatterns.ConditioningBounds
public import NLA.MD06.CubicConfiguration.UniformLaw

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06GraphExcessEncoding
open Reference.MD06CubicConfiguration Reference.MD06BoundedExcess
open Reference.MD06FiniteProbability Reference.MD06JointSupportCounts
open Filter Topology
attribute [local instance] Classical.propDecidable

theorem actual_graph_excess_implies_matched {n M : ℕ}
    (p : SimpleConfiguration n) (h : GraphHasBoundedExcess (configurationGraph p) M) :
    HasBoundedExcess (3*M) p.val := by
  obtain ⟨S,hS,hE⟩ := h
  let P := InducedPattern p S
  let v := (VertexSupport P).card
  let e := P.card
  have hv : v≤S.card := Finset.card_le_card (actual_induced_pattern_support_subset p S)
  have he : S.card+1≤e := by
    simpa only [e,P,actual_induced_pattern_card] using hE
  have heK : e≤3*M := (actual_induced_pattern_edge_bound p S).trans
    (Nat.mul_le_mul_left 3 hS)
  have hve : v<e := by omega
  let shape : ExcessShape (3*M) :=
    ⟨(⟨v,by omega⟩,⟨e,by omega⟩),hve⟩
  let C : ConstraintDatum n shape.val.1.val shape.val.2.val :=
    ⟨P,⟨rfl,rfl,actual_induced_pattern_distinct p S,actual_induced_pattern_disjoint p S⟩⟩
  exact ⟨⟨shape,C⟩,actual_induced_pattern_matches p S⟩

theorem actual_uniform_graph_excess_probability_le (k M : ℕ) :
    GraphProbability k (fun G => GraphHasBoundedExcess G M) ≤
      SimpleExcessProbability k (3*M) := by
  rw [← actual_configuration_conditioned_uniform_graph_law]
  unfold ConditionedGraphProbability SimpleExcessProbability
  apply div_le_div_of_nonneg_right
  · unfold SimpleExcessNumerator
    apply actual_pairing_probability_mono
    intro p hp
    obtain ⟨h,hG⟩ := hp
    exact ⟨h,actual_graph_excess_implies_matched ⟨p,h⟩ hG⟩
  · unfold PairingProbability
    positivity

theorem actual_uniform_graph_excess_probability_nonnegative (k M : ℕ) :
    0 ≤ GraphProbability k (fun G => GraphHasBoundedExcess G M) := by
  rw [← actual_configuration_conditioned_uniform_graph_law]
  unfold ConditionedGraphProbability PairingProbability
  positivity

theorem actual_uniform_graph_excess_probability_limit (M : ℕ) :
    Tendsto (fun k => GraphProbability k (fun G => GraphHasBoundedExcess G M))
      atTop (𝓝 0) := by
  exact squeeze_zero (fun k => actual_uniform_graph_excess_probability_nonnegative k M)
    (fun k => actual_uniform_graph_excess_probability_le k M)
    (actual_simple_excess_probability_limit (3*M))

theorem actual_uniform_graph_excess_inverse_size_bound (M : ℕ) :
    ∀ᶠ k in atTop,
      GraphProbability k (fun G => GraphHasBoundedExcess G M) ≤
        (2*BoundConstant (3*M)/Real.exp (-2))/(Size k : ℝ) := by
  filter_upwards [actual_simple_excess_inverse_size_bound (3*M)] with k hk
  exact (actual_uniform_graph_excess_probability_le k M).trans hk

#print axioms actual_graph_excess_implies_matched
#print axioms actual_uniform_graph_excess_probability_le
#print axioms actual_uniform_graph_excess_probability_nonnegative
#print axioms actual_uniform_graph_excess_probability_limit
#print axioms actual_uniform_graph_excess_inverse_size_bound
end Reference.MD06GraphExcessEncoding
