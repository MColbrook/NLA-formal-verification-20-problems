module

public import NLA.MD06.CubicConfiguration.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CubicConfiguration
open Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def configurationNeighborEquiv {n : ℕ} (p : SimpleConfiguration n)
    (u : Fin n) : Fin 3 ≃ (configurationGraph p).neighborSet u :=
  Equiv.ofBijective (fun a => ⟨(p.val.val (u,a)).fst, ⟨a,rfl⟩⟩)
    ⟨by
      intro a b h
      exact p.property.2 u (congrArg Subtype.val h),
     by
      rintro ⟨v,a,ha⟩
      exact ⟨a,Subtype.ext ha⟩⟩

theorem actual_configuration_graph_cubic {n : ℕ} (p : SimpleConfiguration n) :
    (configurationGraph p).IsRegularOfDegree 3 := by
  intro u
  rw [← (configurationGraph p).card_neighborSet_eq_degree]
  rw [← Fintype.card_congr (configurationNeighborEquiv p u)]
  rfl

theorem actual_neighbor_frames_nonempty {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsRegularOfDegree 3) : Nonempty (NeighborFrames G) := by
  refine ⟨fun u => Fintype.equivOfCardEq ?_⟩
  rw [Fintype.card_fin, G.card_neighborSet_eq_degree, hG.degree_eq]

theorem actual_neighbor_frames_card {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.IsRegularOfDegree 3) : Fintype.card (NeighborFrames G) = 6^n := by
  obtain ⟨f⟩ := actual_neighbor_frames_nonempty G hG
  have hc (u : Fin n) : Fintype.card (Fin 3 ≃ G.neighborSet u) = 6 := by
    rw [Fintype.card_equiv (f u),Fintype.card_fin]
    norm_num
  rw [Fintype.card_pi]
  simp [hc]

#print axioms actual_configuration_graph_cubic
#print axioms actual_neighbor_frames_nonempty
#print axioms actual_neighbor_frames_card
end Reference.MD06CubicConfiguration
