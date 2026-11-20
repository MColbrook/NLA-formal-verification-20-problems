module

public import NLA.MD06.ConditionalPartner.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06AdaptiveExposure
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

noncomputable def ConditionalPairingProbability {n : ℕ}
    (C : Finset (Dart n × Dart n)) (E : Pairing n → Prop) : ℝ :=
  (Fintype.card {p : Pairing n // Matches C p ∧ E p} : ℝ) / (PatternCount C : ℝ)

def ExposedVertices {n : ℕ} (C : Finset (Dart n × Dart n)) : Finset (Fin n) :=
  (UsedDarts C).image Prod.fst

def VertexDarts {n : ℕ} (S : Finset (Fin n)) : Finset (Dart n) :=
  S ×ˢ Finset.univ

end Reference.MD06AdaptiveExposure
