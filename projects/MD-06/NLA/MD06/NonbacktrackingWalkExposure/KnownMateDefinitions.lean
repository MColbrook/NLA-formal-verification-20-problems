module

public import NLA.MD06.NonbacktrackingWalkExposure.ReplyDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration
attribute [local instance] Classical.propDecidable

noncomputable def ConstraintMate {n : ℕ} (C : Finset (Dart n × Dart n)) (a : Dart n) : Dart n :=
  if h : ∃ e : Dart n × Dart n, e∈C ∧ (a=e.1 ∨ a=e.2) then
    let e := Classical.choose h
    if a=e.1 then e.2 else e.1
  else a

end Reference.MD06WalkExposure
