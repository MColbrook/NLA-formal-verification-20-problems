module

public import NLA.MD06.CleanRadiusProbability.FinsetBridge
public import NLA.MD06.CleanRadiusProbability.FiniteProbability
public import NLA.MD06.CleanRadiusCardinality.Radius
public import NLA.MD06.GraphExcessEncoding.GraphProbability

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanRadiusProbability
open Reference.MD06RadiusEmbedding Reference.MD06CleanRadiusCardinality
open Reference.MD06GraphExcessEncoding Reference.MD06FiniteProbability
open Reference.MD06BoundedExcess
open Filter Topology
attribute [local instance] Classical.propDecidable

theorem actual_bad_cycle_radius_graph_excess {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsRegularOfDegree 3) (ell R : ℕ) (hb : BadCycleRadius G ell R) :
    GraphHasBoundedExcess G (ell*2^R) := by
  obtain ⟨v,c,hc,hell,hu⟩ := hb
  refine ⟨(CycleRadius G c R).toFinset,?_,actual_radius_finset_excess c hc R hu⟩
  rw [Set.toFinset_card,←hell]
  exact actual_cycle_radius_card_bound c hc (fun x => hG.degree_eq x) R

theorem actual_bad_cycle_radius_probability_le (k ell R : ℕ) :
    GraphProbability k (fun G => BadCycleRadius G ell R) ≤
      GraphProbability k (fun G => GraphHasBoundedExcess G (ell*2^R)) := by
  apply actual_regular_graph_probability_monotone
  intro G hG hb
  exact actual_bad_cycle_radius_graph_excess G hG ell R hb

theorem actual_bad_cycle_radius_probability_limit (ell R : ℕ) :
    Tendsto (fun k => GraphProbability k (fun G => BadCycleRadius G ell R))
      atTop (𝓝 0) := by
  exact squeeze_zero (fun k => actual_bad_cycle_radius_probability_nonnegative k ell R)
    (fun k => actual_bad_cycle_radius_probability_le k ell R)
    (actual_uniform_graph_excess_probability_limit (ell*2^R))

theorem actual_bad_cycle_radius_inverse_size_bound (ell R : ℕ) :
    ∀ᶠ k in atTop,
      GraphProbability k (fun G => BadCycleRadius G ell R) ≤
        (2*BoundConstant (3*(ell*2^R))/Real.exp (-2))/(Size k : ℝ) := by
  filter_upwards [actual_uniform_graph_excess_inverse_size_bound (ell*2^R)] with k hk
  exact (actual_bad_cycle_radius_probability_le k ell R).trans hk

theorem actual_no_bad_cycle_radius_iff {n : ℕ} (G : SimpleGraph (Fin n)) (ell R : ℕ) :
    (¬BadCycleRadius G ell R) ↔
      ∀v : Fin n,∀c : G.Walk v v,c.IsCycle → c.length=ell → CleanRadius G c R := by
  constructor
  · intro h v c hc hell
    by_contra hn
    exact h ⟨v,c,hc,hell,hn⟩
  · intro h hb
    obtain ⟨v,c,hc,hell,hn⟩ := hb
    exact hn (h v c hc hell)

theorem actual_all_cycle_radii_clean_limit (ell R : ℕ) :
    Tendsto (fun k => GraphProbability k (fun G =>
      ∀v : Fin (Size k),∀c : G.Walk v v,c.IsCycle → c.length=ell → CleanRadius G c R))
      atTop (𝓝 1) := by
  have he (k : ℕ) :
      GraphProbability k (fun G =>
        ∀v : Fin (Size k),∀c : G.Walk v v,c.IsCycle → c.length=ell → CleanRadius G c R)=
        1-GraphProbability k (fun G => BadCycleRadius G ell R) := by
    rw [←actual_graph_probability_complement]
    apply congrArg (GraphProbability k)
    funext G
    exact propext (actual_no_bad_cycle_radius_iff G ell R).symm
  have ht : Tendsto (fun k => (1 : ℝ)-GraphProbability k (fun G => BadCycleRadius G ell R))
      atTop (𝓝 ((1 : ℝ)-0)) :=
    tendsto_const_nhds.sub (actual_bad_cycle_radius_probability_limit ell R)
  simpa only [he,sub_zero] using ht

#print axioms actual_bad_cycle_radius_graph_excess
#print axioms actual_bad_cycle_radius_probability_le
#print axioms actual_bad_cycle_radius_probability_limit
#print axioms actual_bad_cycle_radius_inverse_size_bound
#print axioms actual_no_bad_cycle_radius_iff
#print axioms actual_all_cycle_radii_clean_limit
end Reference.MD06CleanRadiusProbability
