module

public import NLA.MD06.AdaptiveExposure.Definitions
public import NLA.MD06.ConditionalPartner.Proofs

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06AdaptiveExposure
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06PairingCounts
open Reference.MD06ConditionalPartner
attribute [local instance] Classical.propDecidable

theorem actual_vertex_darts_card {n : ℕ} (S : Finset (Fin n)) :
    (VertexDarts S).card = 3*S.card := by
  simp [VertexDarts,Finset.card_product,Dart,Nat.mul_comm]

theorem actual_exposed_vertex_card {n : ℕ} (C : Finset (Dart n × Dart n))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) :
    (ExposedVertices C).card ≤ 2*C.card := by
  calc
    _ ≤ (UsedDarts C).card := Finset.card_image_le
    _ = _ := actual_disjoint_pattern_used_card C hd hdis

theorem actual_conditional_hit_vertices_bound (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k)))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (a : Dart (Size k)) (ha : a ∉ UsedDarts C) (S : Finset (Fin (Size k))) :
    ConditionalPartnerProbability C a (VertexDarts S) ≤
      (3*S.card : ℕ) / (3*Size k-2*C.card-1 : ℕ) := by
  simpa only [actual_vertex_darts_card] using
    actual_conditional_partner_probability_le k C hd hdis a ha (VertexDarts S)

theorem actual_exposure_collision_bound (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k)))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (a : Dart (Size k)) (ha : a ∉ UsedDarts C) :
    ConditionalPartnerProbability C a (VertexDarts (insert a.1 (ExposedVertices C))) ≤
      (3*(2*C.card+1) : ℕ) / (3*Size k-2*C.card-1 : ℕ) := by
  apply (actual_conditional_hit_vertices_bound k C hd hdis a ha _).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Nat.mul_le_mul_left 3
    ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (actual_exposed_vertex_card C hd hdis) 1))

#print axioms actual_vertex_darts_card
#print axioms actual_exposed_vertex_card
#print axioms actual_conditional_hit_vertices_bound
#print axioms actual_exposure_collision_bound
end Reference.MD06AdaptiveExposure
