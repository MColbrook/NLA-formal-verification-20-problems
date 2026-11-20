module

public import NLA.MD06.CubicConfiguration.Definitions
public import NLA.MD06.CyclePairPatterns.Definitions
public import NLA.MD06.CanonicalCyclePatterns.Definitions
public import NLA.MD06.CanonicalCyclePatterns.MeanDefinitions
public import NLA.MD06.CubicConfiguration.UniformDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06GraphCycleEvent
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06PairingCounts

def GraphCycleExists {n : ℕ} (G : SimpleGraph (Fin n)) (ell : ℕ) : Prop :=
  3 ≤ ell ∧ ∃ vertices : Fin ell ↪ Fin n,
    ∀ i : Fin ell, G.Adj (vertices i) (vertices (finRotate ell i))

def RawPairingCycleExists {n : ℕ} (p : Pairing n) (ell : ℕ) : Prop :=
  ∃ D : CycleData n ell, Matches (CyclePattern D) p

def CanonicalPairingCycleExists {n : ℕ} (p : Pairing n) (ell : ℕ) : Prop :=
  ∃ C : CanonicalCycleDatum n ell, Matches C.val p

end Reference.MD06GraphCycleEvent
