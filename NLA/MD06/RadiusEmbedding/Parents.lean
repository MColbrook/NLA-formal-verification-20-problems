module

public import NLA.MD06.RadiusEmbedding.Forest

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem actual_forest_parent_unique (hG : G.IsAcyclic) {root v w z : V}
    (hv : G.Reachable root v) (hw : G.Adj v w) (hz : G.Adj v z)
    (hdw : G.dist root w + 1 = G.dist root v)
    (hdz : G.dist root z + 1 = G.dist root v) : w = z := by
  obtain ⟨p, hp, hplen⟩ := (hv.trans hw.reachable).exists_path_of_dist
  obtain ⟨q, hq, hqlen⟩ := (hv.trans hz.reachable).exists_path_of_dist
  have hpc : (p.concat hw.symm).IsPath := by
    apply Walk.isPath_of_length_eq_dist
    simpa only [Walk.length_concat, hplen] using hdw
  have hqc : (q.concat hz.symm).IsPath := by
    apply Walk.isPath_of_length_eq_dist
    simpa only [Walk.length_concat, hqlen] using hdz
  have he : p.concat hw.symm = q.concat hz.symm :=
    Subtype.mk.inj (hG.subsingleton_path root v |>.elim ⟨_, hpc⟩ ⟨_, hqc⟩)
  simpa only [Walk.penultimate_concat] using congrArg Walk.penultimate he

theorem actual_forest_parent_exists (hG : G.IsAcyclic) {root v : V}
    (hv : G.Reachable root v) (hne : root ≠ v) :
    ∃! w : V, G.Adj v w ∧ G.dist root w + 1 = G.dist root v := by
  obtain ⟨p, hp, hplen⟩ := hv.exists_path_of_dist
  have hnil : ¬p.Nil := by
    intro h
    exact hne h.eq
  have hadj := p.adj_penultimate hnil
  have hdle : G.dist root p.penultimate ≤ G.dist root v - 1 := by
    have := G.dist_le p.dropLast
    simpa only [Walk.length_dropLast, hplen] using this
  have hdist : G.dist root p.penultimate + 1 = G.dist root v := by
    have := hG.dist_eq_dist_add_one_of_adj_of_reachable root hadj.symm hv
    omega
  refine ⟨p.penultimate, ⟨hadj.symm, hdist⟩, ?_⟩
  intro w hw
  exact actual_forest_parent_unique hG hv hw.1 hadj.symm hw.2 hdist

end Reference.MD06RadiusEmbedding
