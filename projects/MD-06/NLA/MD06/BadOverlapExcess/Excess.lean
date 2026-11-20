module

public import NLA.MD06.BadOverlapExcess.Reconstruction

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadOverlap
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
open Reference.MD06BadJointMoments Reference.MD06JointSupportCounts
open Reference.MD06PairingCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_joint_contains_bad {n q : ℕ} (f : JointDatum n q) (i : Fin q) :
    BadPattern (f i) ⊆ JointPattern f := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,he⟩

theorem actual_shared_vertex_has_three_darts {n q : ℕ}
    (f : JointDatum n q) (p : Pairing n) (hm : Matches (JointPattern f) p)
    (i j : Fin q) (hij : i ≠ j) (u : Fin n)
    (hi : u ∈ VertexSupport (BadPattern (f i)))
    (hj : u ∈ VertexSupport (BadPattern (f j))) :
    3 ≤ (LocalSupport (JointPattern f) u).card := by
  by_contra h
  have hc : (LocalSupport (JointPattern f) u).card ≤ 2 := by omega
  have hli : LocalSupport (BadPattern (f i)) u = LocalSupport (JointPattern f) u :=
    Finset.eq_of_subset_of_card_le
      (actual_local_support_mono (actual_joint_contains_bad f i) u)
      (le_trans hc (actual_bad_vertex_min_two (f i) u hi))
  have hlj : LocalSupport (BadPattern (f j)) u = LocalSupport (JointPattern f) u :=
    Finset.eq_of_subset_of_card_le
      (actual_local_support_mono (actual_joint_contains_bad f j) u)
      (le_trans hc (actual_bad_vertex_min_two (f j) u hj))
  have hmi : Matches (BadPattern (f i)) p :=
    fun e he => hm e (actual_joint_contains_bad f i he)
  have hmj : Matches (BadPattern (f j)) p :=
    fun e he => hm e (actual_joint_contains_bad f j he)
  have hf := actual_matched_bad_local_support_injective (f i) (f j) p u
    hmi hmj hi hj (hli.trans hlj.symm)
  exact hij (f.injective hf)

theorem actual_dart_support_card_gt_two_vertices {n : ℕ}
    (C : Finset (Dart n × Dart n))
    (hl : ∀ u ∈ VertexSupport C, 2 ≤ (LocalSupport C u).card)
    (u : Fin n) (hu : u ∈ VertexSupport C) (h3 : 3 ≤ (LocalSupport C u).card) :
    2*(VertexSupport C).card < (DartSupport C).card := by
  have h := Finset.sum_lt_sum
    (s := (Finset.univ : Finset {v : Fin n // v ∈ VertexSupport C}))
    (f := fun _ => (2 : ℕ)) (g := fun v => (LocalSupport C v.val).card)
    (fun v _ => hl v.val v.property)
    ⟨⟨u,hu⟩,Finset.mem_univ _,by change 2 < (LocalSupport C u).card; omega⟩
  calc
    2*(VertexSupport C).card =
        ∑ v : {v : Fin n // v ∈ VertexSupport C}, 2 := by
      simp [Nat.mul_comm]
    _ < ∑ v : {v : Fin n // v ∈ VertexSupport C}, (LocalSupport C v.val).card := h
    _ = (DartSupport C).card := (actual_dart_support_card_sum_local C).symm

theorem actual_overlapping_joint_has_excess {n q : ℕ}
    (f : JointDatum n q) (p : Pairing n) (hm : Matches (JointPattern f) p)
    (i j : Fin q) (hij : i ≠ j) (u : Fin n)
    (hi : u ∈ VertexSupport (BadPattern (f i)))
    (hj : u ∈ VertexSupport (BadPattern (f j))) :
    (VertexSupport (JointPattern f)).card + 1 ≤ (JointPattern f).card := by
  have hu : u ∈ VertexSupport (JointPattern f) := by
    obtain ⟨a,ha⟩ := (actual_mem_vertex_support (BadPattern (f i)) u).mp hi
    exact (actual_mem_vertex_support (JointPattern f) u).mpr
      ⟨a,actual_dart_support_mono (actual_joint_contains_bad f i) ha⟩
  have h3 := actual_shared_vertex_has_three_darts f p hm i j hij u hi hj
  have h := actual_dart_support_card_gt_two_vertices (JointPattern f)
    (actual_joint_vertex_min_two f) u hu h3
  rw [actual_joint_matching_dart_card f p hm] at h
  omega

theorem actual_overlapping_joint_support_bound {n q : ℕ}
    (f : JointDatum n q) (p : Pairing n) (hm : Matches (JointPattern f) p)
    (hi : ∃ i j : Fin q, i ≠ j ∧
      ∃ u : Fin n, u ∈ VertexSupport (BadPattern (f i)) ∧
        u ∈ VertexSupport (BadPattern (f j))) :
    (VertexSupport (JointPattern f)).card + 1 ≤ (JointPattern f).card ∧
      (JointPattern f).card ≤ 2*q := by
  rcases hi with ⟨i,j,hij,u,hui,huj⟩
  exact ⟨actual_overlapping_joint_has_excess f p hm i j hij u hui huj,
    actual_joint_pattern_card_le_two_q f⟩

#print axioms actual_joint_contains_bad
#print axioms actual_shared_vertex_has_three_darts
#print axioms actual_dart_support_card_gt_two_vertices
#print axioms actual_overlapping_joint_has_excess
#print axioms actual_overlapping_joint_support_bound
end Reference.MD06BadOverlap
