module

public import NLA.MD06.JointSupportCounts.SupportProperties
public import NLA.MD06.BadJointMoments.JointCompatibility
public import NLA.MD06.BadPatternCounts.PatternProperties

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06JointSupportCounts
open Reference.MD06Simplicity Reference.MD06CubicConfiguration Reference.MD06BadJointMoments Reference.MD06BadPatternCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_loop_local_support {n : ℕ} (d : LoopDatum n) :
    LocalSupport (LoopPattern d) d.1 = {d.2.val.1,d.2.val.2} := by
  ext a
  simp [LocalSupport,DartSupport,LoopPattern]

theorem actual_loop_vertex_support {n : ℕ} (d : LoopDatum n) :
    VertexSupport (LoopPattern d) = {d.1} := by
  ext u
  simp [VertexSupport,DartSupport,LoopPattern]

theorem actual_two_edge_local_source {n : ℕ} (u v : Fin n) (a b c d : Fin 3)
    (huv : u ≠ v) :
    LocalSupport ({((u,a),(v,c)),((u,b),(v,d))} : Finset (Dart n × Dart n)) u =
      {a,b} := by
  ext x
  simp [LocalSupport,DartSupport,huv,or_comm]

theorem actual_two_edge_local_target {n : ℕ} (u v : Fin n) (a b c d : Fin 3)
    (huv : u ≠ v) :
    LocalSupport ({((u,a),(v,c)),((u,b),(v,d))} : Finset (Dart n × Dart n)) v =
      {c,d} := by
  ext x
  simp [LocalSupport,DartSupport,huv.symm]

theorem actual_two_edge_vertex_support {n : ℕ} (u v : Fin n) (a b c d : Fin 3) :
    VertexSupport ({((u,a),(v,c)),((u,b),(v,d))} : Finset (Dart n × Dart n)) =
      {u,v} := by
  ext x
  simp [VertexSupport,DartSupport]

theorem actual_two_edge_vertex_min_two {n : ℕ} (u v : Fin n) (a b c d : Fin 3)
    (huv : u ≠ v) (hab : a ≠ b) (hcd : c ≠ d) :
    ∀ w ∈ VertexSupport ({((u,a),(v,c)),((u,b),(v,d))} :
        Finset (Dart n × Dart n)),
      2 ≤ (LocalSupport ({((u,a),(v,c)),((u,b),(v,d))} :
        Finset (Dart n × Dart n)) w).card := by
  intro w hw
  rw [actual_two_edge_vertex_support] at hw
  simp only [Finset.mem_insert,Finset.mem_singleton] at hw
  rcases hw with hw | hw
  · subst w
    rw [actual_two_edge_local_source u v a b c d huv]
    simp [hab]
  · subst w
    rw [actual_two_edge_local_target u v a b c d huv]
    simp [hcd]

theorem actual_bad_vertex_min_two {n : ℕ} (z : BadDatum n) :
    ∀ u ∈ VertexSupport (BadPattern z), 2 ≤ (LocalSupport (BadPattern z) u).card := by
  cases z with
  | inl d =>
    intro u hu
    simp only [BadPattern,actual_loop_vertex_support,Finset.mem_singleton] at hu
    subst u
    simp only [BadPattern,actual_loop_local_support]
    simp [ne_of_lt d.2.property]
  | inr d =>
    cases hb : d.2.2.2 with
    | false =>
      simpa only [BadPattern,DoublePattern,hb,Bool.false_eq_true,if_false] using
        actual_two_edge_vertex_min_two d.1.val.1 d.1.val.2
          d.2.1.val.1 d.2.1.val.2 d.2.2.1.val.1 d.2.2.1.val.2
          (ne_of_lt d.1.property) (ne_of_lt d.2.1.property)
          (ne_of_lt d.2.2.1.property)
    | true =>
      simpa only [BadPattern,DoublePattern,hb,if_true] using
        actual_two_edge_vertex_min_two d.1.val.1 d.1.val.2
          d.2.1.val.1 d.2.1.val.2 d.2.2.1.val.2 d.2.2.1.val.1
          (ne_of_lt d.1.property) (ne_of_lt d.2.1.property)
          (ne_of_lt d.2.2.1.property).symm

theorem actual_joint_vertex_min_two {n q : ℕ} (f : JointDatum n q) :
    ∀ u ∈ VertexSupport (JointPattern f),
      2 ≤ (LocalSupport (JointPattern f) u).card := by
  intro u hu
  obtain ⟨a,ha⟩ := (actual_mem_vertex_support (JointPattern f) u).mp hu
  obtain ⟨e,he,hx⟩ := (actual_mem_dart_support (JointPattern f) (u,a)).mp ha
  obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp he
  have hd : (u,a) ∈ DartSupport (BadPattern (f i)) :=
    (actual_mem_dart_support (BadPattern (f i)) (u,a)).mpr ⟨e,he,hx⟩
  have hv : u ∈ VertexSupport (BadPattern (f i)) :=
    (actual_mem_vertex_support (BadPattern (f i)) u).mpr ⟨a,hd⟩
  have hs : BadPattern (f i) ⊆ JointPattern f := by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,he⟩
  exact le_trans (actual_bad_vertex_min_two (f i) u hv)
    (Finset.card_le_card (actual_local_support_mono hs u))

theorem actual_joint_matching_dart_card {n q : ℕ} (f : JointDatum n q)
    (p : Pairing n) (hm : Reference.MD06PairingCounts.Matches (JointPattern f) p) :
    (DartSupport (JointPattern f)).card = 2*(JointPattern f).card := by
  exact actual_dart_support_card_of_disjoint (JointPattern f)
    (actual_joint_pattern_distinct_endpoints f)
    (actual_joint_matching_disjoint_endpoints f p hm)

theorem actual_joint_matching_vertices_le_edges {n q : ℕ} (f : JointDatum n q)
    (p : Pairing n) (hm : Reference.MD06PairingCounts.Matches (JointPattern f) p) :
    (VertexSupport (JointPattern f)).card ≤ (JointPattern f).card := by
  have h := actual_dart_support_card_ge_two_vertices (JointPattern f)
    (actual_joint_vertex_min_two f)
  rw [actual_joint_matching_dart_card f p hm] at h
  omega

theorem actual_bad_pattern_card_le_two {n : ℕ} (z : BadDatum n) :
    (BadPattern z).card ≤ 2 := by
  cases z with
  | inl d => simp only [BadPattern,actual_loop_pattern_card];omega
  | inr d => simpa only [BadPattern,actual_double_pattern_card] using (le_refl 2)

theorem actual_joint_pattern_card_le_two_q {n q : ℕ} (f : JointDatum n q) :
    (JointPattern f).card ≤ 2*q := by
  have h := Finset.card_biUnion_le
    (s := (Finset.univ : Finset (Fin q))) (t := fun i => BadPattern (f i))
  have h2 : (∑ i : Fin q, (BadPattern (f i)).card) ≤ ∑ i : Fin q, 2 :=
    Finset.sum_le_sum (fun i _ => actual_bad_pattern_card_le_two (f i))
  simpa only [JointPattern,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_id,Nat.mul_comm] using le_trans h h2

#print axioms actual_loop_local_support
#print axioms actual_loop_vertex_support
#print axioms actual_two_edge_local_source
#print axioms actual_two_edge_local_target
#print axioms actual_two_edge_vertex_support
#print axioms actual_two_edge_vertex_min_two
#print axioms actual_bad_vertex_min_two
#print axioms actual_joint_vertex_min_two
#print axioms actual_joint_matching_dart_card
#print axioms actual_joint_matching_vertices_le_edges
#print axioms actual_bad_pattern_card_le_two
#print axioms actual_joint_pattern_card_le_two_q
end Reference.MD06JointSupportCounts
