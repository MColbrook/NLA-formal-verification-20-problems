module

public import NLA.IV04.PaperLayerSignDefinitions
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace IV04.Paper.IntegerPartition

def IsVertex (P : IntegerPartition) (q : ℕ → ℝ) : Prop :=
  ∀ i < P.m-1, q i=-1 ∨ q i=1
def InCube (P : IntegerPartition) (q : ℕ → ℝ) : Prop :=
  ∀ i < P.m-1, -1 ≤ q i ∧ q i ≤ 1
def backwardSign (P : IntegerPartition) (q : ℕ → ℝ) (i : ℕ) : ℤ :=
  ∏ j ∈ Finset.Ico i (P.m-1), if q j=-1 then 1 else -1
def vertexSign (P : IntegerPartition) (q : ℕ → ℝ) (i : Fin P.m) : ℤ :=
  P.backwardSign q i.val

end IV04.Paper.IntegerPartition
