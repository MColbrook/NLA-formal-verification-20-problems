module

public import NLA.MD06.DisjointTypedEnumeration.JointBinding
public import NLA.MD06.BadPatternCounts.PatternProperties
public import NLA.MD06.JointSupportCounts.SupportProperties

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06JointSupportCounts
open Reference.MD06BadPatternCounts Reference.MD06BadJointMoments Reference.MD06CubicConfiguration
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_bad_pattern_card {n : ℕ} (z : BadDatum n) :
    (BadPattern z).card = if IsDouble z then 2 else 1 := by
  cases z with
  | inl d => exact actual_loop_pattern_card d
  | inr d => exact actual_double_pattern_card d

theorem actual_bad_pattern_distinct_endpoints {n : ℕ} (z : BadDatum n) :
    ∀e∈BadPattern z,e.1 ≠ e.2 := by
  cases z with
  | inl d => exact actual_loop_pattern_distinct_endpoints d
  | inr d => exact actual_double_pattern_distinct_endpoints d

theorem actual_bad_pattern_disjoint_endpoints {n : ℕ} (z : BadDatum n) :
    ∀e∈BadPattern z,∀f∈BadPattern z,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  cases z with
  | inl d => exact actual_loop_pattern_disjoint_endpoints d
  | inr d => exact actual_double_pattern_disjoint_endpoints d

theorem actual_vertex_disjoint_constraint_endpoints {n : ℕ}
    (C D : Finset (Dart n × Dart n)) (h : Disjoint (VertexSupport C) (VertexSupport D))
    (e : Dart n × Dart n) (he : e ∈ C) (f : Dart n × Dart n) (hf : f ∈ D) :
    Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hc : x ∈ DartSupport C :=
    (actual_mem_dart_support C x).mpr ⟨e,he,by simpa only
      [Finset.mem_insert,Finset.mem_singleton] using hx⟩
  have hd : x ∈ DartSupport D :=
    (actual_mem_dart_support D x).mpr ⟨f,hf,by simpa only
      [Finset.mem_insert,Finset.mem_singleton] using hy⟩
  exact Finset.disjoint_left.mp h
    ((actual_mem_vertex_support C x.1).mpr ⟨x.2,hc⟩)
    ((actual_mem_vertex_support D x.1).mpr ⟨x.2,hd⟩)

theorem actual_vertex_disjoint_constraints {n : ℕ}
    (C D : Finset (Dart n × Dart n)) (h : Disjoint (VertexSupport C) (VertexSupport D)) :
    Disjoint C D := by
  apply Finset.disjoint_left.mpr
  intro e he hd
  have hc := actual_vertex_disjoint_constraint_endpoints C D h e he e hd
  exact Finset.disjoint_left.mp hc (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)

theorem actual_typed_joint_pattern_card {n q : ℕ} (S : Finset (Fin n))
    (b : Fin q → Bool) (f : TypedJoint S b) :
    (JointPattern f.val).card = Weight b := by
  have h := (Reference.MD06BadDisjointDecomposition.actual_no_overlap_iff_vertex_disjoint
    f.val).mp f.property.1
  have hd : (↑(Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint
      (fun i => BadPattern (f.val i)) := by
    intro i _ j _ hij
    exact actual_vertex_disjoint_constraints _ _ (h i j hij)
  rw [JointPattern,Finset.card_biUnion hd]
  simp_rw [actual_bad_pattern_card,f.property.2.1]
  rfl

theorem actual_typed_joint_pattern_distinct_endpoints {n q : ℕ} (S : Finset (Fin n))
    (b : Fin q → Bool) (f : TypedJoint S b) :
    ∀e∈JointPattern f.val,e.1 ≠ e.2 := by
  intro e he
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
  exact actual_bad_pattern_distinct_endpoints (f.val i) e hi

theorem actual_typed_joint_pattern_disjoint_endpoints {n q : ℕ} (S : Finset (Fin n))
    (b : Fin q → Bool) (g : TypedJoint S b) :
    ∀e∈JointPattern g.val,∀f∈JointPattern g.val,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  intro e he f hf hef
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hf
  by_cases hij : i=j
  · subst j
    exact actual_bad_pattern_disjoint_endpoints (g.val i) e hi f hj hef
  · exact actual_vertex_disjoint_constraint_endpoints _ _
      ((Reference.MD06BadDisjointDecomposition.actual_no_overlap_iff_vertex_disjoint
        g.val).mp g.property.1 i j hij) e hi f hj

#print axioms actual_bad_pattern_card
#print axioms actual_bad_pattern_distinct_endpoints
#print axioms actual_bad_pattern_disjoint_endpoints
#print axioms actual_vertex_disjoint_constraint_endpoints
#print axioms actual_vertex_disjoint_constraints
#print axioms actual_typed_joint_pattern_card
#print axioms actual_typed_joint_pattern_distinct_endpoints
#print axioms actual_typed_joint_pattern_disjoint_endpoints
end Reference.MD06DisjointTypedEnumeration
