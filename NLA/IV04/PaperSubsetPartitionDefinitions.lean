module

public import NLA.IV04.PaperPartitionDefinitions
public import Mathlib.Data.Fintype.Sum

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction

/-- Actual subset-sum selection of a finite family of natural weights. -/
def HasSubsetSum {ι : Type*} [Fintype ι] (w : ι → ℕ) (t : ℕ) : Prop :=
  ∃ selected : ι → Bool, (∑ i, if selected i then w i else 0) = t

def IsSigned {ι : Type*} (s : ι → ℤ) : Prop := ∀ i, s i = -1 ∨ s i = 1

def signedTotal {ι : Type*} [Fintype ι] (w : ι → ℕ) (s : ι → ℤ) : ℤ :=
  ∑ i, s i * (w i : ℤ)

def SignedPartition {ι : Type*} [Fintype ι] (w : ι → ℕ) : Prop :=
  ∃ s, IsSigned s ∧ signedTotal w s = 0

/-- Two positive padding weights avoid both zero-weight and target-range exceptions. -/
def subsetPartitionWeights {ι : Type*} [Fintype ι] (w : ι → ℕ) (t : ℕ) : ι ⊕ Bool → ℕ
  | Sum.inl i => w i
  | Sum.inr false => (∑ i, w i) + 2*t + 1
  | Sum.inr true => 2*(∑ i, w i) + 1

end IV04.Paper.Computational.SATReduction