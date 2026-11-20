module

public import NLA.MD06.RadiusEmbedding.BranchStep

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def BinaryFrames (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3) :
    (j : ℕ) → (hj : 1 ≤ j) → (hjR : j ≤ R) →
      Fin (2 ^ (j - 1)) ≃ (DistanceLayer G root j)
  | 0, hj, _ => False.elim (by omega)
  | 1, _, _ => (Finset.equivFinOfCardEq (show (DistanceLayer G root 1).card = 1 by
      rw [actual_distance_layer_one_eq_neighbors, card_neighborFinset_eq_degree, hroot])).symm
  | j + 2, _, hjR => by
      let prev := BinaryFrames hG root R hroot hinterior (j + 1) (by omega) (by omega)
      have hd : ∀ v ∈ DistanceLayer G root (j + 1), G.degree v = 3 := by
        intro v hv
        have hrv := (Finset.mem_filter.mp hv).2
        apply hinterior v hrv.1
        · omega
        · omega
      have hpow : 2 ^ (j + 2 - 1) = 2 ^ (j + 1 - 1) * 2 := by
        have he : j + 2 - 1 = (j + 1 - 1) + 1 := by omega
        rw [he, Nat.pow_succ]
      exact (finCongr hpow).trans
        (SuccessorCoordinate hG root (j + 1) _ (by omega) prev hd)
termination_by j => j

theorem actual_binary_frames_member (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3)
    (j : ℕ) (hj : 1 ≤ j) (hjR : j ≤ R) (b : Fin (2 ^ (j - 1))) :
    G.Reachable root (BinaryFrames hG root R hroot hinterior j hj hjR b).val ∧
      G.dist root (BinaryFrames hG root R hroot hinterior j hj hjR b).val = j := by
  exact (Finset.mem_filter.mp (BinaryFrames hG root R hroot hinterior j hj hjR b).property).2

theorem actual_binary_frames_one_adj (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3)
    (hR : 1 ≤ R) (b : Fin (2 ^ (1 - 1))) :
    G.Adj root (BinaryFrames hG root R hroot hinterior 1 (by omega) hR b).val := by
  exact dist_eq_one_iff_adj.mp (actual_binary_frames_member hG root R hroot hinterior 1
    (by omega) hR b).2

end Reference.MD06RadiusEmbedding
