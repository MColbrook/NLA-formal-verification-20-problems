module

public import NLA.MD06.RadiusEmbedding.BinaryFrames

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem branch_parent_index_lt {j b : ℕ} (hj : 1 ≤ j) (hb : b < 2 ^ j) :
    b / 2 < 2 ^ (j - 1) := by
  have he : j = (j - 1) + 1 := by omega
  have hp : 2 ^ j = 2 ^ (j - 1) * 2 := by
    conv_lhs => rw [he, Nat.pow_succ]
  omega

theorem binary_step_power (j : ℕ) :
    2 ^ (j + 2 - 1) = 2 ^ (j + 1 - 1) * 2 := by
  have he : j + 2 - 1 = (j + 1 - 1) + 1 := by omega
  rw [he, Nat.pow_succ]

theorem actual_binary_frames_successor (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3)
    (j : ℕ) (hjR : j + 2 ≤ R)
    (hd : ∀ v ∈ DistanceLayer G root (j + 1), G.degree v = 3) :
    BinaryFrames hG root R hroot hinterior (j + 2) (by omega) hjR =
      (finCongr (binary_step_power j)).trans
        (SuccessorCoordinate hG root (j + 1) _ (by omega)
          (BinaryFrames hG root R hroot hinterior (j + 1) (by omega) (by omega)) hd) := by
  rw [BinaryFrames]

theorem actual_binary_frames_parent_adj (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3)
    (j : ℕ) (hj : 1 ≤ j) (hjR : j + 1 ≤ R) (b : Fin (2 ^ j)) :
    G.Adj
      (BinaryFrames hG root R hroot hinterior j hj (by omega)
        ⟨b.val / 2, branch_parent_index_lt hj b.isLt⟩).val
      (BinaryFrames hG root R hroot hinterior (j + 1) (by omega) hjR
        (Fin.cast (by simp) b)).val := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hd : ∀ v ∈ DistanceLayer G root (k + 1), G.degree v = 3 := by
    intro v hv
    have hrv := (Finset.mem_filter.mp hv).2
    apply hinterior v hrv.1
    · omega
    · omega
  rw [actual_binary_frames_successor hG root R hroot hinterior k hjR hd]
  have hadj := actual_successor_coordinate_parent hG root (k + 1) _ (by omega)
    (BinaryFrames hG root R hroot hinterior (k + 1) (by omega) (by omega)) hd
    ((finCongr (binary_step_power k)) (Fin.cast (by simp) b))
  convert hadj using 1
  · congr 1
  · rfl

end Reference.MD06RadiusEmbedding
