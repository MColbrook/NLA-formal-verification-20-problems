module

public import NLA.MD06.MixedPatternShapes.BadCycleDefinitions
public import NLA.MD06.CanonicalCyclePatterns.MeanDefinitions
public import Mathlib.Data.Sum.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedLowCycleBijections
open Reference.MD06MixedPatternShapes Reference.MD06CanonicalCyclePatterns
open Reference.MD06CyclePairPatterns Reference.MD06Simplicity
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def LoopCanonicalDatum {n : ℕ} (d : LoopDatum n) : CanonicalCycleDatum n 1 :=
  ⟨CanonicalCyclePattern (LoopCycle d),⟨LoopCycle d,rfl⟩⟩

def DoubleCanonicalDatum {n : ℕ} (d : DoubleDatum n) : CanonicalCycleDatum n 2 :=
  ⟨CanonicalCyclePattern (DoubleCycle d),⟨DoubleCycle d,rfl⟩⟩

abbrev TypedDatum (n ell : ℕ) :=
  (CanonicalCycleDatum n 1⊕CanonicalCycleDatum n 2)⊕CanonicalCycleDatum n ell

def TypedMap {n ell : ℕ} (d : MarkedDatum n ell) : TypedDatum n ell :=
  Sum.map (Sum.map LoopCanonicalDatum DoubleCanonicalDatum) id d

def TypedPattern {n ell : ℕ} (d : TypedDatum n ell) : Finset (Dart n×Dart n) :=
  match d with
  | Sum.inl (Sum.inl C) => C.val
  | Sum.inl (Sum.inr C) => C.val
  | Sum.inr C => C.val

def MarkedMatchingCount {n ell : ℕ} (p : Pairing n) : ℕ :=
  Fintype.card {d : MarkedDatum n ell // Matches (MarkedPattern d) p}

def MeanMarkedCount (k ell : ℕ) : ℝ :=
  (∑ p : Pairing (Size k),(MarkedMatchingCount (ell:=ell) p : ℝ)) /
    (Fintype.card (Pairing (Size k)) : ℝ)
end Reference.MD06MixedLowCycleBijections
