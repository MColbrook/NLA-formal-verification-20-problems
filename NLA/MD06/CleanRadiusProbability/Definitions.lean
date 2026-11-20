module

public import NLA.MD06.RadiusEmbedding.PaperGeometry
public import NLA.MD06.GraphExcessEncoding.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanRadiusProbability
open Reference.MD06RadiusEmbedding
attribute [local instance] Classical.propDecidable

def BadCycleRadius {n : ℕ} (G : SimpleGraph (Fin n)) (ell R : ℕ) : Prop :=
  ∃ v : Fin n, ∃ c : G.Walk v v,
    c.IsCycle ∧ c.length=ell ∧ ¬CleanRadius G c R

end Reference.MD06CleanRadiusProbability
