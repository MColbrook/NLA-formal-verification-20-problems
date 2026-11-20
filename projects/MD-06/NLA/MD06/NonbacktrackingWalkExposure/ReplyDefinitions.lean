module

public import NLA.MD06.NonbacktrackingWalkExposure.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

noncomputable def ReplyStep {n : ℕ} (s : ExposureState n) (i : Fin 2) (b : Dart n) : ExposureState n :=
  { current := PortChoice b i
    exposed := if s.current ∉ UsedDarts s.exposed then insert (s.current,b) s.exposed else s.exposed
    visited := insert b.1 s.visited
    collisions := s.collisions + if s.current ∉ UsedDarts s.exposed ∧ b.1 ∈ s.visited then 1 else 0 }

end Reference.MD06WalkExposure
