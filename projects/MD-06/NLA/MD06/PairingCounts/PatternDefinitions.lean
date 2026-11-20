module

public import NLA.MD06.PairingCounts.MateDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06PairingCounts
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

def UsedDarts {n : ℕ} (C : Finset (Dart n × Dart n)) : Finset (Dart n) :=
  C.biUnion (fun e => {e.1,e.2})

def Matches {n : ℕ} (C : Finset (Dart n × Dart n)) (p : Pairing n) : Prop :=
  ∀ e ∈ C, p.val e.1 = e.2

noncomputable def PatternCount {n : ℕ} (C : Finset (Dart n × Dart n)) : ℕ :=
  Fintype.card {p : Pairing n // Matches C p}

noncomputable def ConstrainedMateCount {n : ℕ}
    (C : Finset (Dart n × Dart n)) (a b : Dart n) : ℕ :=
  Fintype.card {p : Pairing n // Matches C p ∧ p.val a = b}

end Reference.MD06PairingCounts