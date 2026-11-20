module

public import NLA.MD06.PairingCounts.PatternDefinitions
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06ConditionalPartner
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

def FreePartners {n : ℕ} (C : Finset (Dart n × Dart n)) (a : Dart n) : Finset (Dart n) :=
  Finset.univ \ insert a (UsedDarts C)

noncomputable def ConditionalPartnerProbability {n : ℕ}
    (C : Finset (Dart n × Dart n)) (a : Dart n) (B : Finset (Dart n)) : ℝ :=
  (Fintype.card {p : Pairing n // Matches C p ∧ p.val a ∈ B} : ℝ) /
    (PatternCount C : ℝ)

end Reference.MD06ConditionalPartner
