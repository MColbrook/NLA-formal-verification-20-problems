module

public import NLA.MD06.BadDisjointDecomposition.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06CubicConfiguration Reference.MD06JointSupportCounts
open scoped BigOperators

abbrev VertexPair {n : ℕ} (S : Finset (Fin n)) :=
  {uv : ↥S × ↥S // uv.1.val < uv.2.val}

abbrev SupportedLoop {n : ℕ} (S : Finset (Fin n)) :=
  {d : LoopDatum n // VertexSupport (LoopPattern d) ⊆ S}

abbrev SupportedDouble {n : ℕ} (S : Finset (Fin n)) :=
  {d : DoubleDatum n // VertexSupport (DoublePattern d) ⊆ S}

def IsDouble {n : ℕ} : BadDatum n → Bool
  | .inl _ => false
  | .inr _ => true

def Weight {q : ℕ} (b : Fin q → Bool) : ℕ :=
  ∑ i : Fin q, if b i then 2 else 1

abbrev TypedTuple {n q : ℕ} (S : Finset (Fin n)) (b : Fin q → Bool) :=
  {g : Fin q → BadDatum n //
    (∀ i, IsDouble (g i) = b i) ∧
    (∀ i, VertexSupport (BadPattern (g i)) ⊆ S) ∧
    ∀ i j : Fin q, i ≠ j →
      Disjoint (VertexSupport (BadPattern (g i))) (VertexSupport (BadPattern (g j)))}

end Reference.MD06DisjointTypedEnumeration
