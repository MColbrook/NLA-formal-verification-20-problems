module

public import NLA.MD06.GraphCycleWalk.Definitions
public import NLA.MD06.CombinedZeroProbability.GraphBinding

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06GraphCycleWalk
open SimpleGraph Reference.MD06GraphCycleEvent Reference.MD06FiniteProbability
open Reference.MD06CombinedZero
open Filter Topology
attribute [local instance] Classical.propDecidable

theorem actual_cyclic_vertex_parametrization_copy {n ell : ℕ}
    (G : SimpleGraph (Fin n)) (h3 : 3≤ell) (vertices : Fin ell ↪ Fin n)
    (ha : ∀i : Fin ell,G.Adj (vertices i) (vertices (finRotate ell i))) :
    Nonempty (SimpleGraph.Copy (cycleGraph ell) G) := by
  let : NeZero ell := ⟨by omega⟩
  let f : cycleGraph ell →g G :=
    { toFun := vertices
      map_rel' := by
        intro i j hij
        rcases cycleGraph_adj'.mp hij with h | h
        · have he : i-j=(1 : Fin ell) := by
            apply Fin.ext
            simpa [Fin.val_one,Nat.mod_eq_of_lt (show 1<ell by omega)] using h
          have hi : i=finRotate ell j := by
            rw [finRotate_apply]
            simpa only [add_comm] using (sub_eq_iff_eq_add).mp he
          rw [hi]
          exact (ha j).symm
        · have he : j-i=(1 : Fin ell) := by
            apply Fin.ext
            simpa [Fin.val_one,Nat.mod_eq_of_lt (show 1<ell by omega)] using h
          have hj : j=finRotate ell i := by
            rw [finRotate_apply]
            simpa only [add_comm] using (sub_eq_iff_eq_add).mp he
          rw [hj]
          exact ha i }
  exact ⟨⟨f,vertices.injective⟩⟩

theorem actual_graph_cycle_to_walk {n ell : ℕ} (G : SimpleGraph (Fin n))
    (h : GraphCycleExists G ell) : WalkCycleExists G ell := by
  obtain ⟨h3,vertices,ha⟩ := h
  exact (cycleGraph_isContained_iff (by omega : 2<ell)).mp
    (actual_cyclic_vertex_parametrization_copy G h3 vertices ha)

theorem actual_walk_cycle_to_graph {n ell : ℕ} (G : SimpleGraph (Fin n))
    (h : WalkCycleExists G ell) : GraphCycleExists G ell := by
  obtain ⟨v,c,hc,hell⟩ := h
  have h3 : 3≤ell := hell ▸ hc.three_le_length
  let : NeZero ell := ⟨by omega⟩
  obtain ⟨f⟩ := (cycleGraph_isContained_iff (by omega : 2<ell)).mpr ⟨v,c,hc,hell⟩
  refine ⟨h3,f.toEmbedding,?_⟩
  intro i
  apply f.toHom.map_rel
  rw [cycleGraph_adj']
  right
  rw [finRotate_apply,add_sub_cancel_left]
  change 1%ell=1
  exact Nat.mod_eq_of_lt (by omega)

theorem actual_graph_cycle_walk_iff {n ell : ℕ} (G : SimpleGraph (Fin n)) :
    GraphCycleExists G ell ↔ WalkCycleExists G ell :=
  ⟨actual_graph_cycle_to_walk G,actual_walk_cycle_to_graph G⟩

theorem actual_no_graph_cycle_walk_probability_eq (k ell : ℕ) :
    GraphProbability k (fun G => ¬GraphCycleExists G ell)=
      GraphProbability k (fun G => ¬WalkCycleExists G ell) := by
  apply congrArg (GraphProbability k)
  funext G
  exact propext (not_congr (actual_graph_cycle_walk_iff G))

theorem actual_uniform_no_walk_cycle_limit (ell : ℕ) (h3 : 3≤ell) :
    Tendsto (fun k => GraphProbability k (fun G => ¬WalkCycleExists G ell))
      atTop (𝓝 (Real.exp (-((2 : ℝ)^ell/(2*ell))))) := by
  simpa only [actual_no_graph_cycle_walk_probability_eq] using
    actual_uniform_simple_cubic_no_cycle_limit ell h3

#print axioms actual_cyclic_vertex_parametrization_copy
#print axioms actual_graph_cycle_to_walk
#print axioms actual_walk_cycle_to_graph
#print axioms actual_graph_cycle_walk_iff
#print axioms actual_no_graph_cycle_walk_probability_eq
#print axioms actual_uniform_no_walk_cycle_limit
end Reference.MD06GraphCycleWalk
