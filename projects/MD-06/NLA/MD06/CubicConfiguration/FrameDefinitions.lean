module

public import NLA.MD06.CubicConfiguration.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CubicConfiguration

noncomputable def framePartner {n : ℕ} {G : SimpleGraph (Fin n)}
    (f : NeighborFrames G) (x : Dart n) : Dart n :=
  ((f x.fst x.snd).val,
    (f (f x.fst x.snd).val).symm ⟨x.fst, (f x.fst x.snd).property.symm⟩)

end Reference.MD06CubicConfiguration
