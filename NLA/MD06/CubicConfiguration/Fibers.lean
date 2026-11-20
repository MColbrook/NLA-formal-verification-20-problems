module

public import NLA.MD06.CubicConfiguration.CubicFrames
public import NLA.MD06.CubicConfiguration.FramesConstruction

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CubicConfiguration
attribute [local instance] Classical.propDecidable

noncomputable def configurationFrames {n : ℕ} (p : SimpleConfiguration n)
    {G : SimpleGraph (Fin n)} (h : configurationGraph p = G) : NeighborFrames G := by
  subst G
  exact configurationNeighborEquiv p

theorem actual_configuration_frame_val {n : ℕ} (p : SimpleConfiguration n)
    {G : SimpleGraph (Fin n)} (h : configurationGraph p = G)
    (u : Fin n) (a : Fin 3) :
    (configurationFrames p h u a).val = (p.val.val (u,a)).fst := by
  subst G
  rfl

theorem actual_frame_partner_recovers {n : ℕ} (p : SimpleConfiguration n)
    {G : SimpleGraph (Fin n)} (h : configurationGraph p = G) (x : Dart n) :
    framePartner (configurationFrames p h) x = p.val.val x := by
  rcases x with ⟨u,a⟩
  unfold framePartner
  apply Prod.ext
  · exact actual_configuration_frame_val p h u a
  · apply (configurationFrames p h (configurationFrames p h u a).val).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    simp only [actual_configuration_frame_val]
    simpa only [Prod.mk.eta] using
      (congrArg Prod.fst (p.val.property.1 (u,a))).symm

noncomputable def configurationFiberEquiv {n : ℕ} (G : SimpleGraph (Fin n)) :
    {p : SimpleConfiguration n // configurationGraph p = G} ≃ NeighborFrames G where
  toFun p := configurationFrames p.val p.property
  invFun f := ⟨framesConfiguration f, actual_frames_configuration_graph f⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Equiv.ext
    intro x
    exact actual_frame_partner_recovers p.val p.property x
  right_inv f := by
    funext u
    apply Equiv.ext
    intro a
    apply Subtype.ext
    rw [actual_configuration_frame_val]
    rfl

theorem actual_simple_cubic_configuration_fiber_card {n : ℕ}
    (G : SimpleGraph (Fin n)) (hG : G.IsRegularOfDegree 3) :
    Fintype.card {p : SimpleConfiguration n // configurationGraph p = G} = 6^n := by
  rw [Fintype.card_congr (configurationFiberEquiv G)]
  exact actual_neighbor_frames_card G hG

#print axioms actual_configuration_frame_val
#print axioms actual_frame_partner_recovers
#print axioms actual_simple_cubic_configuration_fiber_card
end Reference.MD06CubicConfiguration
