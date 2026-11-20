module

public import NLA.MD06.PairingCounts.ProductDefinitions
public import NLA.MD06.CubicConfiguration.CanonicalPairing

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06PatternUnions
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

noncomputable def UnionPatternCount {I : Type*} [Fintype I] {n : ℕ}
    (C : I → Finset (Dart n × Dart n)) : ℕ :=
  Fintype.card {p : Pairing n // ∃ i : I, Matches (C i) p}

end Reference.MD06PatternUnions