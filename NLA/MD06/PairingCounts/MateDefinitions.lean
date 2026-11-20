module

public import NLA.MD06.PairingCounts.PureRelabel
public import NLA.MD06.CubicConfiguration.UniformDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06PairingCounts
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

noncomputable def MateCount {n : ℕ} (a b : Dart n) : ℕ :=
  Fintype.card {p : Pairing n // p.val a = b}

end Reference.MD06PairingCounts