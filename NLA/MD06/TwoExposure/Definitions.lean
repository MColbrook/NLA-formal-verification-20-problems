module

public import NLA.MD06.AdaptiveExposure.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06TwoExposure
open Reference.MD06CubicConfiguration
attribute [local instance] Classical.propDecidable

def TwoExposureHit {n : ℕ} (a : Dart n) (B : Finset (Dart n))
    (next : Dart n → Dart n) (D : Dart n → Finset (Dart n)) (p : Pairing n) : Prop :=
  p.val a ∈ B ∧ p.val (next (p.val a)) ∈ D (p.val a)

end Reference.MD06TwoExposure
