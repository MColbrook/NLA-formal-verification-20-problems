module

public import NLA.MD06.RadiusEmbedding.PaperObstruction
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
universe u_1
namespace Reference.MD06RadiusEmbeddingInterface
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_unique_cycle_deletion_forest :
∀ {V : Type u_1} {G : SimpleGraph V} {v : V} (c : G.Walk v v),
  Reference.MD06RadiusEmbedding.UniqueCycleEdges c → (G.deleteEdges {e | e ∈ c.edges}).IsAcyclic :=
  Reference.MD06RadiusEmbedding.actual_unique_cycle_deletion_forest
#print axioms actual_unique_cycle_deletion_forest

theorem actual_unique_cycle_forest_roots_separated :
∀ {V : Type u_1} {G : SimpleGraph V} {v u w : V} (c : G.Walk v v),
  Reference.MD06RadiusEmbedding.UniqueCycleEdges c →
    G.Connected → u ∈ c.support → w ∈ c.support → (G.deleteEdges {e | e ∈ c.edges}).Reachable u w → u = w :=
  Reference.MD06RadiusEmbedding.actual_unique_cycle_forest_roots_separated
#print axioms actual_unique_cycle_forest_roots_separated

theorem actual_unique_cycle_forest_root_existsUnique :
∀ {V : Type u_1} {G : SimpleGraph V} {v x : V} (c : G.Walk v v),
  Reference.MD06RadiusEmbedding.UniqueCycleEdges c →
    G.Connected → ∃! u, u ∈ c.support ∧ (G.deleteEdges {e | e ∈ c.edges}).Reachable x u :=
  Reference.MD06RadiusEmbedding.actual_unique_cycle_forest_root_existsUnique
#print axioms actual_unique_cycle_forest_root_existsUnique

theorem actual_forest_parent_unique :
∀ {V : Type u_1} {G : SimpleGraph V},
  G.IsAcyclic →
    ∀ {root v w z : V},
      G.Reachable root v →
        G.Adj v w → G.Adj v z → G.dist root w + 1 = G.dist root v → G.dist root z + 1 = G.dist root v → w = z :=
  Reference.MD06RadiusEmbedding.actual_forest_parent_unique
#print axioms actual_forest_parent_unique

theorem actual_forest_parent_exists :
∀ {V : Type u_1} {G : SimpleGraph V},
  G.IsAcyclic → ∀ {root v : V}, G.Reachable root v → root ≠ v → ∃! w, G.Adj v w ∧ G.dist root w + 1 = G.dist root v :=
  Reference.MD06RadiusEmbedding.actual_forest_parent_exists
#print axioms actual_forest_parent_exists

theorem actual_forest_forward_children_card_two :
∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {G : SimpleGraph V},
  G.IsAcyclic →
    ∀ {root v : V},
      G.Reachable root v → root ≠ v → G.degree v = 3 → (Reference.MD06RadiusEmbedding.ForwardChildren G root v).card = 2 :=
  Reference.MD06RadiusEmbedding.actual_forest_forward_children_card_two
#print axioms actual_forest_forward_children_card_two

theorem actual_forest_binary_layer_card :
∀ {V : Type u_1} [inst : Fintype V] [DecidableEq V] {G : SimpleGraph V},
  G.IsAcyclic →
    ∀ (root : V) (R : ℕ),
      G.degree root = 1 →
        (∀ (v : V), G.Reachable root v → 0 < G.dist root v → G.dist root v < R → G.degree v = 3) →
          ∀ (j : ℕ), 1 ≤ j → j ≤ R → (Reference.MD06RadiusEmbedding.DistanceLayer G root j).card = 2 ^ (j - 1) :=
  Reference.MD06RadiusEmbedding.actual_forest_binary_layer_card
#print axioms actual_forest_binary_layer_card

theorem actual_unique_cycle_radius_iff_forest_distance :
∀ {V : Type u_1} {G : SimpleGraph V} {v x r : V} (c : G.Walk v v),
  Reference.MD06RadiusEmbedding.UniqueCycleEdges c →
    G.Connected →
      r ∈ c.support →
        (G.deleteEdges {e | e ∈ c.edges}).Reachable x r →
          ∀ (R : ℕ),
            x ∈ Reference.MD06RadiusEmbedding.CycleRadius G c R ↔ (G.deleteEdges {e | e ∈ c.edges}).dist x r ≤ R :=
  Reference.MD06RadiusEmbedding.actual_unique_cycle_radius_iff_forest_distance
#print axioms actual_unique_cycle_radius_iff_forest_distance

theorem actual_short_walk_cycle_radius_support :
∀ {V : Type u_1} {G : SimpleGraph V} {v x u : V} (c : G.Walk v v) (R : ℕ),
  u ∈ c.support →
    ∀ (p : G.Walk x u), p.length ≤ R → ∀ y ∈ p.support, y ∈ Reference.MD06RadiusEmbedding.CycleRadius G c R :=
  Reference.MD06RadiusEmbedding.actual_short_walk_cycle_radius_support
#print axioms actual_short_walk_cycle_radius_support

theorem actual_cycle_radius_induced_connected :
∀ {V : Type u_1} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (R : ℕ),
  (SimpleGraph.induce (Reference.MD06RadiusEmbedding.CycleRadius G c R) G).Connected :=
  Reference.MD06RadiusEmbedding.actual_cycle_radius_induced_connected
#print axioms actual_cycle_radius_induced_connected

theorem actual_lifted_cycle_isCycle :
∀ {V : Type u_1} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (R : ℕ),
  c.IsCycle → (Reference.MD06RadiusEmbedding.LiftedCycle c R).IsCycle :=
  Reference.MD06RadiusEmbedding.actual_lifted_cycle_isCycle
#print axioms actual_lifted_cycle_isCycle

theorem actual_clean_radius_root_forest_degree_one :
∀ {V : Type u_1} {G : SimpleGraph V} [inst : Fintype V] [inst_1 : DecidableEq V] {v : V} (c : G.Walk v v) (R : ℕ),
  1 ≤ R →
    Reference.MD06RadiusEmbedding.CleanRadius G c R →
      (∀ (x : V), G.degree x = 3) →
        ∀ r ∈ (Reference.MD06RadiusEmbedding.LiftedCycle c R).support,
          ((SimpleGraph.induce (Reference.MD06RadiusEmbedding.CycleRadius G c R) G).deleteEdges
                  {e | e ∈ (Reference.MD06RadiusEmbedding.LiftedCycle c R).edges}).degree
              r =
            1 :=
  Reference.MD06RadiusEmbedding.actual_clean_radius_root_forest_degree_one
#print axioms actual_clean_radius_root_forest_degree_one

theorem actual_clean_radius_interior_forest_degree_three :
∀ {V : Type u_1} {G : SimpleGraph V} [inst : Fintype V] [inst_1 : DecidableEq V] {v : V} (c : G.Walk v v) (R : ℕ),
  Reference.MD06RadiusEmbedding.CleanRadius G c R →
    (∀ (x : V), G.degree x = 3) →
      ∀ (r x : ↑(Reference.MD06RadiusEmbedding.CycleRadius G c R)),
        r ∈ (Reference.MD06RadiusEmbedding.LiftedCycle c R).support →
          ((SimpleGraph.induce (Reference.MD06RadiusEmbedding.CycleRadius G c R) G).deleteEdges
                  {e | e ∈ (Reference.MD06RadiusEmbedding.LiftedCycle c R).edges}).Reachable
              r x →
            0 <
                ((SimpleGraph.induce (Reference.MD06RadiusEmbedding.CycleRadius G c R) G).deleteEdges
                      {e | e ∈ (Reference.MD06RadiusEmbedding.LiftedCycle c R).edges}).dist
                  r x →
              ((SimpleGraph.induce (Reference.MD06RadiusEmbedding.CycleRadius G c R) G).deleteEdges
                        {e | e ∈ (Reference.MD06RadiusEmbedding.LiftedCycle c R).edges}).dist
                    r x <
                  R →
                ((SimpleGraph.induce (Reference.MD06RadiusEmbedding.CycleRadius G c R) G).deleteEdges
                        {e | e ∈ (Reference.MD06RadiusEmbedding.LiftedCycle c R).edges}).degree
                    x =
                  3 :=
  Reference.MD06RadiusEmbedding.actual_clean_radius_interior_forest_degree_three
#print axioms actual_clean_radius_interior_forest_degree_three

theorem actual_clean_radius_total_layer_card :
∀ {V : Type u_1} [inst : Fintype V] [inst_1 : DecidableEq V] {G : SimpleGraph V} {v : V} (c : G.Walk v v) (R : ℕ),
  1 ≤ R →
    Reference.MD06RadiusEmbedding.CleanRadius G c R →
      (∀ (x : V), G.degree x = 3) →
        ∀ (j : ℕ), 1 ≤ j → j ≤ R → (Reference.MD06RadiusEmbedding.RadiusRootLayer G c R j).card = c.length * 2 ^ (j - 1) :=
  Reference.MD06RadiusEmbedding.actual_clean_radius_total_layer_card
#print axioms actual_clean_radius_total_layer_card

theorem actual_radius_forest_closed_interior :
∀ {V : Type u_1} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (R : ℕ)
  (r x : ↑(Reference.MD06RadiusEmbedding.CycleRadius G c R)),
  r ∈ (Reference.MD06RadiusEmbedding.LiftedCycle c R).support →
    (Reference.MD06RadiusEmbedding.RadiusForest G c R).Reachable r x →
      (Reference.MD06RadiusEmbedding.RadiusForest G c R).dist r x < R →
        G.neighborSet ↑x ⊆ Reference.MD06RadiusEmbedding.CycleRadius G c R :=
  Reference.MD06RadiusEmbedding.actual_radius_forest_closed_interior
#print axioms actual_radius_forest_closed_interior

theorem actual_radius_forest_bounded_root :
∀ {V : Type u_1} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (R : ℕ)
  (x : ↑(Reference.MD06RadiusEmbedding.CycleRadius G c R)),
  ∃ r ∈ (Reference.MD06RadiusEmbedding.LiftedCycle c R).support,
    (Reference.MD06RadiusEmbedding.RadiusForest G c R).Reachable r x ∧
      (Reference.MD06RadiusEmbedding.RadiusForest G c R).dist r x ≤ R :=
  Reference.MD06RadiusEmbedding.actual_radius_forest_bounded_root
#print axioms actual_radius_forest_bounded_root

theorem actual_clean_radius_root_unique_bounded :
∀ {V : Type u_1} {G : SimpleGraph V} {v : V} (c : G.Walk v v) (R : ℕ),
  Reference.MD06RadiusEmbedding.CleanRadius G c R →
    ∀ (x : ↑(Reference.MD06RadiusEmbedding.CycleRadius G c R)),
      ∃! r,
        r ∈ (Reference.MD06RadiusEmbedding.LiftedCycle c R).support ∧
          (Reference.MD06RadiusEmbedding.RadiusForest G c R).Reachable r x ∧
            (Reference.MD06RadiusEmbedding.RadiusForest G c R).dist r x ≤ R :=
  Reference.MD06RadiusEmbedding.actual_clean_radius_root_unique_bounded
#print axioms actual_clean_radius_root_unique_bounded

theorem actual_clean_radius_embedding_exists :
∀ {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n} (c : G.Walk v v),
  c.IsCycle →
    ∀ (R : ℕ) (hR : 4 ≤ R),
      4 ≤ c.length →
        Reference.MD06RadiusEmbedding.CleanRadius G c R →
          (∀ (x : Fin n), G.degree x = 3) → Nonempty (Reference.MD06CleanCycle.CleanCycleEmbedding (ell := c.length) G hR) :=
  Reference.MD06RadiusEmbedding.actual_clean_radius_embedding_exists
#print axioms actual_clean_radius_embedding_exists

theorem actual_clean_radius_nonsynchronized_local_minimum :
∀ {n : ℕ} (G : SimpleGraph (Fin n)) {v : Fin n} (c : G.Walk v v),
  c.IsCycle →
    G.Connected →
      (∀ (x : Fin n), G.degree x = 3) →
        4 ≤ c.length →
          4 ∣ c.length →
            ∀ (R : ℕ),
              4 ≤ R →
                Reference.MD06RadiusEmbedding.CleanRadius G c R →
                  ∀ (gamma : ℝ),
                    0 < gamma →
                      ∀ (hn : 2 ≤ n),
                        gamma ≤ Reference.MD06Spectral.LaplacianGap G hn →
                          32 * ↑c.length / (√(1 - Reference.MD06CycleProfile.Root 4 ^ 2) ^ 4 * gamma ^ 2) <
                              2 ^ (R - 1) →
                            ∃ phi : Reference.MD06Correction.Configuration n,
                              (∀ (i : Fin n),
                                  Reference.MD06Actual.Gradient G (Reference.MD06Actual.PhaseLift fun a => phi.ofLp a)
                                      i =
                                    0) ∧
                                IsLocalMin (Reference.MD06Actual.Energy G)
                                    (Reference.MD06Actual.PhaseLift fun a => phi.ofLp a) ∧
                                  ¬Reference.MD06Actual.Synchronized
                                        (Reference.MD06Actual.PhaseLift fun a => phi.ofLp a) ∧
                                    (∀ (i j : Fin n), G.Adj i j → 1 / 32 < Real.cos (phi.ofLp i - phi.ofLp j)) ∧
                                      ∀ (z : Reference.MD06Correction.Configuration n),
                                        ∑ i, z.ofLp i = 0 →
                                          √(1 - Reference.MD06CycleProfile.Root 4 ^ 2) * gamma / 2 * ‖z‖ ^ 2 ≤
                                            Reference.MD06Actual.HessianQuadratic G
                                              (Reference.MD06Actual.PhaseLift fun a => phi.ofLp a) fun i => z.ofLp i :=
  Reference.MD06RadiusEmbedding.actual_clean_radius_nonsynchronized_local_minimum
#print axioms actual_clean_radius_nonsynchronized_local_minimum

theorem actual_clean_radius_literal_stable_nonsync :
∀ {n : ℕ} (G : SimpleGraph (Fin n)) {v : Fin n} (c : G.Walk v v),
  c.IsCycle →
    G.Connected →
      (∀ (x : Fin n), G.degree x = 3) →
        4 ≤ c.length →
          4 ∣ c.length →
            ∀ (R : ℕ),
              4 ≤ R →
                Reference.MD06RadiusEmbedding.CleanRadius G c R →
                  ∀ (gamma : ℝ),
                    1 / 10 ≤ gamma →
                      ∀ (hn : 2 ≤ n),
                        gamma ≤ Reference.MD06Spectral.LaplacianGap G hn →
                          32 * ↑c.length / (√(1 - Reference.MD06CycleProfile.Root 4 ^ 2) ^ 4 * gamma ^ 2) <
                              2 ^ (R - 1) →
                            ∃ theta,
                              (∀ (i : Fin n), Reference.MD06Actual.Gradient G theta i = 0) ∧
                                IsLocalMin (Reference.MD06Actual.Energy G) theta ∧
                                  ¬Reference.MD06Actual.Synchronized theta ∧
                                    (∀ (i j : Fin n), G.Adj i j → 1 / 32 < (theta i - theta j).cos) ∧
                                      ∀ (z : Fin n → ℝ),
                                        ∑ i, z i = 0 →
                                          1 / 320 * ∑ i, z i ^ 2 ≤ Reference.MD06Actual.HessianQuadratic G theta z :=
  Reference.MD06RadiusEmbedding.actual_clean_radius_literal_stable_nonsync
#print axioms actual_clean_radius_literal_stable_nonsync

theorem actual_clean_radius_exact_obstruction :
∀ {n : ℕ} (G : SimpleGraph (Fin n)) {v : Fin n} (cycle : G.Walk v v),
  cycle.IsCycle →
    G.Connected →
      (∀ (x : Fin n), G.degree x = 3) →
        4 ≤ cycle.length →
          4 ∣ cycle.length →
            ∀ (R : ℕ),
              4 ≤ R →
                Reference.MD06RadiusEmbedding.CleanRadius G cycle R →
                  ∀ (gamma : ℝ),
                    0 < gamma →
                      ∀ (hn : 2 ≤ n),
                        gamma ≤ Reference.MD06Spectral.LaplacianGap G hn →
                          32 * ↑cycle.length / (√(1 - Reference.MD06CycleProfile.Root 4 ^ 2) ^ 4 * gamma ^ 2) <
                              2 ^ (R - 1) →
                            ∃ theta,
                              (∀ (i : Fin n), Reference.MD06Actual.Gradient G theta i = 0) ∧
                                IsLocalMin (Reference.MD06Actual.Energy G) theta ∧
                                  ¬Reference.MD06Actual.Synchronized theta ∧
                                    (∀ (i j : Fin n),
                                        G.Adj i j →
                                          √(1 - Reference.MD06CycleProfile.Root 4 ^ 2) / 2 ≤ (theta i - theta j).cos) ∧
                                      ∀ (z : Fin n → ℝ),
                                        ∑ i, z i = 0 →
                                          √(1 - Reference.MD06CycleProfile.Root 4 ^ 2) * gamma / 2 * ∑ i, z i ^ 2 ≤
                                            Reference.MD06Actual.HessianQuadratic G theta z :=
  Reference.MD06RadiusEmbedding.actual_clean_radius_exact_obstruction
#print axioms actual_clean_radius_exact_obstruction

theorem actual_cubic_dimension :
∀ {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n), (∀ (x : Fin n), G.degree x = 3) → 4 ≤ n :=
  Reference.MD06RadiusEmbedding.actual_cubic_dimension
#print axioms actual_cubic_dimension

theorem actual_paper_md_obstruction :
∀ {n : ℕ} (G : SimpleGraph (Fin n)) {v : Fin n} (cycle : G.Walk v v),
  cycle.IsCycle →
    G.Connected →
      (∀ (x : Fin n), G.degree x = 3) →
        0 < cycle.length →
          4 ∣ cycle.length →
            ∀ (R : ℕ),
              4 ≤ R →
                Reference.MD06RadiusEmbedding.CleanRadius G cycle R →
                  ∀ (gamma : ℝ),
                    0 < gamma →
                      gamma ≤ Reference.MD06RadiusEmbedding.TotalLaplacianGap G →
                        32 * ↑cycle.length / (√(1 - Reference.MD06CycleProfile.Root 4 ^ 2) ^ 4 * gamma ^ 2) <
                            2 ^ (R - 1) →
                          ∃ theta,
                            (∀ (i : Fin n), Reference.MD06Actual.Gradient G theta i = 0) ∧
                              IsLocalMin (Reference.MD06Actual.Energy G) theta ∧
                                ¬Reference.MD06Actual.Synchronized theta ∧
                                  (∀ (i j : Fin n),
                                      G.Adj i j →
                                        √(1 - Reference.MD06CycleProfile.Root 4 ^ 2) / 2 ≤ (theta i - theta j).cos) ∧
                                    ∀ (z : Fin n → ℝ),
                                      ∑ i, z i = 0 →
                                        √(1 - Reference.MD06CycleProfile.Root 4 ^ 2) * gamma / 2 * ∑ i, z i ^ 2 ≤
                                          Reference.MD06Actual.HessianQuadratic G theta z :=
  Reference.MD06RadiusEmbedding.actual_paper_md_obstruction
#print axioms actual_paper_md_obstruction

end Reference.MD06RadiusEmbeddingInterface
