module

public import NLA.MD06.RadiusEmbedding.BinaryFrameParents
public import NLA.MD06.RadiusEmbedding.CycleEnumeration

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

abbrev BranchNodes (R : ℕ) := (j : Fin (R + 1)) × Fin (2 ^ (j.val - 1))

noncomputable def FrameValue (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3)
    (x : BranchNodes R) : V :=
  if h0 : x.1.val = 0 then root else
    (BinaryFrames hG root R hroot hinterior x.1.val (by omega)
      (by have hx := x.1.isLt; omega) x.2).val

theorem actual_frame_value_reachable_distance (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3) (x : BranchNodes R) :
    G.Reachable root (FrameValue hG root R hroot hinterior x) ∧
      G.dist root (FrameValue hG root R hroot hinterior x) = x.1.val := by
  unfold FrameValue
  split_ifs with h0
  · exact ⟨.refl root, by simp only [dist_self, h0]⟩
  · exact actual_binary_frames_member hG root R hroot hinterior _ _ _ _

theorem actual_frame_value_injective (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3) :
    Function.Injective (FrameValue hG root R hroot hinterior) := by
  intro x y heq
  have hx := actual_frame_value_reachable_distance hG root R hroot hinterior x
  have hy := actual_frame_value_reachable_distance hG root R hroot hinterior y
  have hdepth : x.1 = y.1 := Fin.ext (by rw [heq] at hx; omega)
  rcases x with ⟨j,b⟩
  rcases y with ⟨k,d⟩
  dsimp at hdepth
  subst k
  have hb : b = d := by
    by_cases h0 : j.val = 0
    · apply Fin.ext
      have hp : 2 ^ (j.val - 1) = 1 := by rw [h0]; rfl
      have hbi := b.isLt
      have hdi := d.isLt
      omega
    · simp only [FrameValue, dif_neg h0] at heq
      exact (BinaryFrames hG root R hroot hinterior j.val (by omega)
        (by have hj := j.isLt; omega)).injective (Subtype.ext heq)
  subst d
  rfl

theorem actual_frame_value_surjective_truncation (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3)
    (v : V) (hv : G.Reachable root v) (hbound : G.dist root v ≤ R) :
    ∃ x : BranchNodes R, FrameValue hG root R hroot hinterior x = v := by
  by_cases h0 : G.dist root v = 0
  · have he : root = v := by
      rcases (dist_eq_zero_iff_eq_or_not_reachable.mp h0) with h | h
      · exact h
      · exact (h hv).elim
    refine ⟨⟨⟨0,by omega⟩,⟨0,by simp⟩⟩, ?_⟩
    simp only [FrameValue]
    exact he
  · have hj : 1 ≤ G.dist root v := by omega
    have hm : v ∈ DistanceLayer G root (G.dist root v) := by
      simp only [DistanceLayer, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hv, trivial⟩
    let b := (BinaryFrames hG root R hroot hinterior _ hj hbound).symm ⟨v,hm⟩
    refine ⟨⟨⟨G.dist root v,by omega⟩,b⟩, ?_⟩
    simp only [FrameValue, dif_neg h0]
    exact congrArg Subtype.val ((BinaryFrames hG root R hroot hinterior _ hj hbound).apply_symm_apply ⟨v,hm⟩)

end Reference.MD06RadiusEmbedding
