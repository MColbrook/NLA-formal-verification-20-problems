module

public import NLA.MD06.JointSupportCounts.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06JointSupportCounts
open Reference.MD06CubicConfiguration
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_mem_dart_support {n : ℕ} (C : Finset (Dart n × Dart n)) (x : Dart n) :
    x ∈ DartSupport C ↔ ∃ e ∈ C, x = e.1 ∨ x = e.2 := by
  simp only [DartSupport,Finset.mem_biUnion,Finset.mem_insert,Finset.mem_singleton]

theorem actual_mem_vertex_support {n : ℕ} (C : Finset (Dart n × Dart n)) (u : Fin n) :
    u ∈ VertexSupport C ↔ ∃ a : Fin 3, (u,a) ∈ DartSupport C := by
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨⟨v,a⟩,ha,hvu⟩
    change v = u at hvu
    subst v
    exact ⟨a,ha⟩
  · rintro ⟨a,ha⟩
    exact Finset.mem_image.mpr ⟨(u,a),ha,rfl⟩

theorem actual_mem_local_support {n : ℕ} (C : Finset (Dart n × Dart n))
    (u : Fin n) (a : Fin 3) :
    a ∈ LocalSupport C u ↔ (u,a) ∈ DartSupport C := by
  simp only [LocalSupport,Finset.mem_filter,Finset.mem_univ,true_and]

theorem actual_dart_support_mono {n : ℕ} {C D : Finset (Dart n × Dart n)}
    (h : C ⊆ D) : DartSupport C ⊆ DartSupport D := by
  intro x hx
  rcases (actual_mem_dart_support C x).mp hx with ⟨e,he,hx⟩
  exact (actual_mem_dart_support D x).mpr ⟨e,h he,hx⟩

theorem actual_local_support_mono {n : ℕ} {C D : Finset (Dart n × Dart n)}
    (h : C ⊆ D) (u : Fin n) : LocalSupport C u ⊆ LocalSupport D u := by
  intro a ha
  exact (actual_mem_local_support D u a).mpr
    (actual_dart_support_mono h ((actual_mem_local_support C u a).mp ha))

theorem actual_dart_support_card_of_disjoint {n : ℕ} (C : Finset (Dart n × Dart n))
    (hd : ∀ e ∈ C, e.1 ≠ e.2)
    (hj : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) :
    (DartSupport C).card = 2*C.card := by
  have hp : (↑C : Set (Dart n × Dart n)).PairwiseDisjoint
      (fun e => ({e.1,e.2} : Finset (Dart n))) := by
    intro e he f hf hef
    exact hj e he f hf hef
  rw [DartSupport,Finset.card_biUnion hp]
  have hc : (∑ e ∈ C, ({e.1,e.2} : Finset (Dart n)).card) = ∑ e ∈ C, 2 := by
    apply Finset.sum_congr rfl
    intro e he
    simp [hd e he]
  rw [hc]
  simp [Nat.mul_comm]

theorem actual_dart_support_card_sum_local {n : ℕ} (C : Finset (Dart n × Dart n)) :
    (DartSupport C).card =
      ∑ u : {v : Fin n // v ∈ VertexSupport C}, (LocalSupport C u.val).card := by
  let e : {x : Dart n // x ∈ DartSupport C} ≃
      (Σ u : {v : Fin n // v ∈ VertexSupport C},
        {a : Fin 3 // a ∈ LocalSupport C u.val}) :=
    { toFun := fun x => ⟨
        ⟨x.val.1,(actual_mem_vertex_support C x.val.1).mpr ⟨x.val.2,x.property⟩⟩,
        ⟨x.val.2,(actual_mem_local_support C x.val.1 x.val.2).mpr x.property⟩⟩
      invFun := fun x => ⟨(x.1.val,x.2.val),
        (actual_mem_local_support C x.1.val x.2.val).mp x.2.property⟩
      left_inv := by rintro ⟨⟨u,a⟩,h⟩;rfl
      right_inv := by rintro ⟨⟨u,hu⟩,a,ha⟩;rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma] at h
  simpa only [Fintype.card_coe] using h

theorem actual_dart_support_card_ge_two_vertices {n : ℕ}
    (C : Finset (Dart n × Dart n))
    (hl : ∀ u ∈ VertexSupport C, 2 ≤ (LocalSupport C u).card) :
    2*(VertexSupport C).card ≤ (DartSupport C).card := by
  have h := Finset.sum_le_sum
    (s := (Finset.univ : Finset {v : Fin n // v ∈ VertexSupport C}))
    (fun u _ => hl u.val u.property)
  calc
    2*(VertexSupport C).card =
        ∑ u : {v : Fin n // v ∈ VertexSupport C}, 2 := by
      simp [Nat.mul_comm]
    _ ≤ ∑ u : {v : Fin n // v ∈ VertexSupport C}, (LocalSupport C u.val).card := h
    _ = (DartSupport C).card := (actual_dart_support_card_sum_local C).symm

#print axioms actual_mem_dart_support
#print axioms actual_mem_vertex_support
#print axioms actual_mem_local_support
#print axioms actual_dart_support_mono
#print axioms actual_local_support_mono
#print axioms actual_dart_support_card_of_disjoint
#print axioms actual_dart_support_card_sum_local
#print axioms actual_dart_support_card_ge_two_vertices
end Reference.MD06JointSupportCounts
