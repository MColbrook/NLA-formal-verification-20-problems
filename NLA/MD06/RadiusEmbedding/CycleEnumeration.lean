module

public import NLA.MD06.RadiusEmbedding.BranchStep

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

noncomputable def CycleRootMap {v : V} (c : G.Walk v v) :
    Fin c.length → c.support.toFinset := fun i =>
  ⟨c.getVert i.val, List.mem_toFinset.mpr (c.getVert_mem_support _)⟩

theorem actual_cycle_root_map_bijective {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    Function.Bijective (CycleRootMap c) := by
  constructor
  · intro i j h
    apply Fin.ext
    apply hc.getVert_injOn' (by have hi := i.isLt; simp only [Set.mem_ofPred_eq]; omega)
      (by have hj := j.isLt; simp only [Set.mem_ofPred_eq]; omega)
    exact congrArg Subtype.val h
  · intro x
    obtain ⟨i, he, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (List.mem_toFinset.mp x.property)
    by_cases hl : i < c.length
    · refine ⟨⟨i,hl⟩, Subtype.ext ?_⟩
      exact he
    · have hei : i = c.length := by omega
      refine ⟨⟨0, by have hlen := hc.three_le_length; omega⟩, Subtype.ext ?_⟩
      change c.getVert 0 = x.val
      rw [Walk.getVert_zero]
      simpa only [hei, Walk.getVert_length] using he

noncomputable def CycleRootCoordinate {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    Fin c.length ≃ c.support.toFinset :=
  Equiv.ofBijective _ (actual_cycle_root_map_bijective c hc)

def NextCycleIndex {ell : ℕ} (i : Fin ell) : Fin ell :=
  ⟨(i.val + 1) % ell, Nat.mod_lt _ (by have hi := i.isLt; omega)⟩

def PreviousCycleIndex {ell : ℕ} (i : Fin ell) : Fin ell :=
  ⟨(i.val + ell - 1) % ell, Nat.mod_lt _ (by have hi := i.isLt; omega)⟩

theorem actual_cycle_coordinate_next_adj {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (i : Fin c.length) :
    c.toSubgraph.Adj (CycleRootCoordinate c hc i).val
      (CycleRootCoordinate c hc (NextCycleIndex i)).val := by
  change c.toSubgraph.Adj (c.getVert i.val) (c.getVert ((i.val+1)%c.length))
  by_cases hi : i.val + 1 < c.length
  · rw [Nat.mod_eq_of_lt hi]
    exact c.toSubgraph_adj_getVert i.isLt
  · have he : i.val + 1 = c.length := by have hb := i.isLt; omega
    rw [he, Nat.mod_self, Walk.getVert_zero]
    simpa only [he, Walk.getVert_length] using c.toSubgraph_adj_getVert i.isLt

theorem actual_cycle_coordinate_neighbor_set {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (i : Fin c.length) :
    c.toSubgraph.neighborSet (CycleRootCoordinate c hc i).val =
      {(CycleRootCoordinate c hc (PreviousCycleIndex i)).val,
       (CycleRootCoordinate c hc (NextCycleIndex i)).val} := by
  change c.toSubgraph.neighborSet (c.getVert i.val) =
    {c.getVert ((i.val+c.length-1)%c.length), c.getVert ((i.val+1)%c.length)}
  have hlen := hc.three_le_length
  by_cases hzero : i.val = 0
  · rw [hzero, Walk.getVert_zero, hc.neighborSet_toSubgraph_endpoint]
    have hp : (0+c.length-1)%c.length = c.length-1 := by
      simpa only [Nat.zero_add] using Nat.mod_eq_of_lt (show c.length-1 < c.length by omega)
    have hn : (0+1)%c.length = 1 := Nat.mod_eq_of_lt (by omega)
    rw [hp, hn]
    exact Set.pair_comm _ _
  · rw [hc.neighborSet_toSubgraph_internal hzero i.isLt]
    have hp : (i.val+c.length-1)%c.length = i.val-1 := by
      have he : i.val+c.length-1 = (i.val-1)+c.length := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by have hi := i.isLt; omega)]
    rw [hp]
    by_cases hlast : i.val+1 < c.length
    · rw [Nat.mod_eq_of_lt hlast]
    · have he : i.val+1 = c.length := by have hi := i.isLt; omega
      rw [he, Nat.mod_self, Walk.getVert_length, Walk.getVert_zero]

end Reference.MD06RadiusEmbedding
