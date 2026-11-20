module

public import NLA.MD06.CubicConfiguration.FrameDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CubicConfiguration

theorem actual_frame_partner_involutive {n : ℕ} {G : SimpleGraph (Fin n)}
    (f : NeighborFrames G) : Function.Involutive (framePartner f) := by
  rintro ⟨u,a⟩
  let w := (f u a).val
  let b := (f w).symm ⟨u,(f u a).property.symm⟩
  have hb : f w b = ⟨u,(f u a).property.symm⟩ :=
    (f w).apply_symm_apply _
  change framePartner f (w,b) = (u,a)
  have hv : (f w b).val = u := congrArg Subtype.val hb
  unfold framePartner
  apply Prod.ext
  · exact hv
  · change (f (f w b).val).symm ⟨w,(f w b).property.symm⟩ = a
    apply (f (f w b).val).symm_apply_eq.mpr
    apply Subtype.ext
    change w = (f (f w b).val a).val
    rw [hv]

noncomputable def framesPairing {n : ℕ} {G : SimpleGraph (Fin n)}
    (f : NeighborFrames G) : Pairing n :=
  ⟨(actual_frame_partner_involutive f).toPerm (framePartner f), by
    constructor
    · exact actual_frame_partner_involutive f
    · intro x hx
      have hv := congrArg Prod.fst hx
      change (f x.fst x.snd).val = x.fst at hv
      exact (f x.fst x.snd).property.ne' hv⟩

noncomputable def framesConfiguration {n : ℕ} {G : SimpleGraph (Fin n)}
    (f : NeighborFrames G) : SimpleConfiguration n :=
  ⟨framesPairing f, by
    constructor
    · intro u a
      change (f u a).val ≠ u
      exact (f u a).property.ne'
    · intro u a b h
      apply (f u).injective
      exact Subtype.ext h⟩

theorem actual_frames_configuration_graph {n : ℕ} {G : SimpleGraph (Fin n)}
    (f : NeighborFrames G) : configurationGraph (framesConfiguration f) = G := by
  ext u v
  change (∃ a : Fin 3, (f u a).val = v) ↔ G.Adj u v
  constructor
  · rintro ⟨a,h⟩
    have ha : G.Adj u (f u a).val := (f u a).property
    exact h ▸ ha
  · intro h
    refine ⟨(f u).symm ⟨v,h⟩, ?_⟩
    exact congrArg Subtype.val ((f u).apply_symm_apply ⟨v,h⟩)

#print axioms actual_frame_partner_involutive
#print axioms actual_frames_configuration_graph
end Reference.MD06CubicConfiguration
