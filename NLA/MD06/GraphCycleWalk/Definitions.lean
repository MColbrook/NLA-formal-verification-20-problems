module

public import NLA.MD06.GraphCycleEvent.Definitions
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06GraphCycleWalk
open SimpleGraph
attribute [local instance] Classical.propDecidable

def WalkCycleExists {n : ℕ} (G : SimpleGraph (Fin n)) (ell : ℕ) : Prop :=
  ∃ v : Fin n, ∃ c : G.Walk v v,c.IsCycle ∧ c.length=ell

end Reference.MD06GraphCycleWalk
