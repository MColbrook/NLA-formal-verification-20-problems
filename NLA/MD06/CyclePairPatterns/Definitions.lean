module

public import NLA.MD06.PairingCounts.ProductDefinitions
public import Mathlib.Logic.Equiv.Fin.Rotate

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CyclePairPatterns
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06PairingCounts
open scoped BigOperators

abbrev LocalFrame := {ab : Fin 3 × Fin 3 // ab.1 ≠ ab.2}
abbrev CycleAssignment (ell : ℕ) := Fin ell → LocalFrame
abbrev CycleData (n ell : ℕ) := (Fin ell ↪ Fin n) × CycleAssignment ell

def outgoing {n ell : ℕ} (D : CycleData n ell) (i : Fin ell) : Dart n :=
  (D.1 i,(D.2 i).val.2)

def incoming {n ell : ℕ} (D : CycleData n ell) (i : Fin ell) : Dart n :=
  (D.1 i,(D.2 i).val.1)

def cycleEdge {n ell : ℕ} (D : CycleData n ell) (i : Fin ell) : Dart n × Dart n :=
  (outgoing D i,incoming D (finRotate ell i))

def CyclePattern {n ell : ℕ} (D : CycleData n ell) : Finset (Dart n × Dart n) :=
  Finset.univ.image (cycleEdge D)

end Reference.MD06CyclePairPatterns