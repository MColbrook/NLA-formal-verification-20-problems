module

public import NLA.MD06.RadiusEmbedding.Children
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def DistanceLayer (G : SimpleGraph V) (root : V) (j : ℕ) : Finset V :=
  Finset.univ.filter (fun x => G.Reachable root x ∧ G.dist root x = j)

omit [DecidableEq V] in
theorem actual_distance_layer_one_eq_neighbors (root : V) :
    DistanceLayer G root 1 = G.neighborFinset root := by
  ext x
  simp only [DistanceLayer, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_neighborFinset, dist_eq_one_iff_adj]
  exact ⟨fun h => h.2, fun h => ⟨h.reachable, h⟩⟩

theorem actual_forest_layer_succ_biUnion (hG : G.IsAcyclic) (root : V) (j : ℕ) :
    DistanceLayer G root (j + 1) =
      (DistanceLayer G root j).biUnion (ForwardChildren G root) := by
  ext x
  simp only [DistanceLayer, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, ForwardChildren, mem_neighborFinset]
  constructor
  · rintro ⟨hx, hd⟩
    have hne : root ≠ x := by
      intro h
      subst x
      simp only [dist_self] at hd
      omega
    obtain ⟨v, hv, _⟩ := actual_forest_parent_exists hG hx hne
    refine ⟨v, ⟨hx.trans hv.1.reachable, ?_⟩, hv.1.symm, ?_⟩
    · omega
    · omega
  · rintro ⟨v, ⟨hv, hdv⟩, hvx, hdx⟩
    exact ⟨hv.trans hvx.reachable, by omega⟩

omit [DecidableEq V] in
theorem actual_forest_layer_children_pairwise_disjoint (hG : G.IsAcyclic)
    (root : V) (j : ℕ) :
    (↑(DistanceLayer G root j) : Set V).PairwiseDisjoint (ForwardChildren G root) := by
  intro v hv w hw hne
  have hv' : G.Reachable root v := by
    exact (Finset.mem_filter.mp hv).2.1
  have hw' : G.Reachable root w := by
    exact (Finset.mem_filter.mp hw).2.1
  exact actual_forest_distinct_parents_disjoint_children hG hv' hw' hne

theorem actual_forest_layer_card_doubles (hG : G.IsAcyclic) (root : V) (j : ℕ)
    (hj : 1 ≤ j) (hd : ∀ v ∈ DistanceLayer G root j, G.degree v = 3) :
    (DistanceLayer G root (j + 1)).card = 2 * (DistanceLayer G root j).card := by
  rw [actual_forest_layer_succ_biUnion hG,
    Finset.card_biUnion (actual_forest_layer_children_pairwise_disjoint hG root j)]
  calc
    ∑ v ∈ DistanceLayer G root j, (ForwardChildren G root v).card =
        ∑ _v ∈ DistanceLayer G root j, 2 := by
      apply Finset.sum_congr rfl
      intro v hv
      have hrv : G.Reachable root v ∧ G.dist root v = j :=
        (Finset.mem_filter.mp hv).2
      have hne : root ≠ v := by
        intro heq
        subst v
        simp only [dist_self] at hrv
        omega
      exact actual_forest_forward_children_card_two hG hrv.1 hne (hd v hv)
    _ = 2 * (DistanceLayer G root j).card := by simp [Nat.mul_comm]

theorem actual_forest_binary_layer_card (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3)
    (j : ℕ) (hj : 1 ≤ j) (hjR : j ≤ R) :
    (DistanceLayer G root j).card = 2 ^ (j - 1) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    by_cases hbase : j = 1
    · subst j
      rw [actual_distance_layer_one_eq_neighbors, card_neighborFinset_eq_degree, hroot]
      rfl
    · have hpred : 1 ≤ j - 1 := by omega
      have hprev : (DistanceLayer G root (j - 1)).card = 2 ^ (j - 1 - 1) :=
        ih (j - 1) (by omega) hpred (by omega)
      have hdeg : ∀ v ∈ DistanceLayer G root (j - 1), G.degree v = 3 := by
        intro v hv
        have hrv : G.Reachable root v ∧ G.dist root v = j - 1 :=
          (Finset.mem_filter.mp hv).2
        apply hinterior v hrv.1
        · omega
        · omega
      have hdouble := actual_forest_layer_card_doubles hG root (j - 1) hpred hdeg
      have he : j - 1 + 1 = j := by omega
      rw [he, hprev] at hdouble
      rw [hdouble]
      have hexp : j - 1 = (j - 1 - 1) + 1 := by omega
      rw [hexp, Nat.pow_succ]
      exact Nat.mul_comm _ _

end Reference.MD06RadiusEmbedding
