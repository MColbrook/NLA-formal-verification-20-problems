module

public import NLA.MD06.SupportedCanonicalCycles.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06SupportedCanonicalCycles
open Reference.MD06JointSupportCounts

def CycleWeight {q : ℕ} (L : Fin q→ℕ) : ℕ := ∑i,L i

def CycleSymmetryFactor {q : ℕ} (L : Fin q→ℕ) : ℕ := ∏i,2*L i

def CanonicalChoiceTree (n : ℕ) :
    (q : ℕ)→(S : Finset (Fin n))→(L : Fin q→ℕ)→Type
  | 0,_,_ => PUnit
  | q+1,S,L =>
    Σ C : SupportedCanonicalCycle S (L 0),
      CanonicalChoiceTree n q (S\VertexSupport C.val.val) (Fin.tail L)

attribute [local instance] Classical.propDecidable

noncomputable instance canonicalChoiceTreeFintype (n q : ℕ) (S : Finset (Fin n))
    (L : Fin q→ℕ) : Fintype (CanonicalChoiceTree n q S L) := by
  induction q generalizing S with
  | zero => change Fintype PUnit;infer_instance
  | succ q ih =>
    letI : ∀ C : SupportedCanonicalCycle S (L 0),
        Fintype (CanonicalChoiceTree n q (S\VertexSupport C.val.val) (Fin.tail L)) :=
      fun C => ih (S\VertexSupport C.val.val) (Fin.tail L)
    change Fintype (Σ C : SupportedCanonicalCycle S (L 0),
      CanonicalChoiceTree n q (S\VertexSupport C.val.val) (Fin.tail L))
    infer_instance

#print axioms canonicalChoiceTreeFintype
end Reference.MD06SupportedCanonicalCycles
