module

public import NLA.MD06.BoundedExcessPatterns.Definitions
public import NLA.MD06.CubicConfiguration.UniformDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06BoundedExcess
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev ExcessShape (K : ℕ) := {s : Fin (K+1)×Fin (K+1) // s.1.val<s.2.val}
abbrev BoundedDatum (n K : ℕ) :=
  Σs : ExcessShape K,ConstraintDatum n s.val.1.val s.val.2.val
instance boundedDatumFintype (n K : ℕ) : Fintype (BoundedDatum n K) :=
  Fintype.ofFinite _
def TotalConstraintCount (n K : ℕ) : ℕ :=
  ∑s : ExcessShape K,ConstraintCount n s.val.1.val s.val.2.val
def TotalConstraintMean (n K : ℕ) : ℝ :=
  (TotalConstraintCount n K : ℝ)/(Fintype.card (Pairing n) : ℝ)
def HasBoundedExcess {n : ℕ} (K : ℕ) (p : Pairing n) : Prop :=
  ∃C : BoundedDatum n K,Matches C.2.val p
def ExcessProbability (k K : ℕ) : ℝ :=
  PairingProbability (Size k) (HasBoundedExcess K)

#print axioms boundedDatumFintype
end Reference.MD06BoundedExcess
