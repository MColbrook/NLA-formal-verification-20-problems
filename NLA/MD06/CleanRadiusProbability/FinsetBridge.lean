module

public import NLA.MD06.CleanRadiusProbability.Definitions
public import NLA.MD06.CleanRadiusCardinality.Excess

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanRadiusProbability
open Reference.MD06RadiusEmbedding Reference.MD06CleanRadiusCardinality
attribute [local instance] Classical.propDecidable

theorem actual_radius_finset_excess {n : ℕ} {G : SimpleGraph (Fin n)}
    {v : Fin n} (c : G.Walk v v) (hc : c.IsCycle) (R : ℕ)
    (hunclean : ¬CleanRadius G c R) :
    (CycleRadius G c R).toFinset.card+1 ≤
      (G.induce ((CycleRadius G c R).toFinset : Set (Fin n))).edgeFinset.card := by
  have hset : ((CycleRadius G c R).toFinset : Set (Fin n))=CycleRadius G c R := by
    ext x
    exact Set.mem_toFinset
  let iso : G.induce ((CycleRadius G c R).toFinset : Set (Fin n)) ≃g
      G.induce (CycleRadius G c R) :=
    { toEquiv := Set.equivOfEq hset
      map_rel_iff' := by intro x y; rfl }
  have hcard := iso.card_edgeFinset_eq
  rw [Set.toFinset_card,hcard]
  exact actual_unclean_radius_excess_edges c hc R hunclean

#print axioms actual_radius_finset_excess
end Reference.MD06CleanRadiusProbability
