module

public import NLA.MD06.RadiusEmbedding.RadiusClosure
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def ChildCoordinate (root v : V)
    (hcard : (ForwardChildren G root v).card = 2) :
    Fin 2 ≃ (ForwardChildren G root v) :=
  (Finset.equivFinOfCardEq hcard).symm

omit [DecidableEq V] in
theorem actual_branch_child_member (root v : V)
    (hcard : (ForwardChildren G root v).card = 2) (a : Fin 2) :
    G.Adj v (ChildCoordinate root v hcard a).val ∧
      G.dist root (ChildCoordinate root v hcard a).val = G.dist root v + 1 := by
  have := (ChildCoordinate root v hcard a).property
  simpa only [ForwardChildren, Finset.mem_filter, mem_neighborFinset] using this

noncomputable def SuccessorPairMap (hG : G.IsAcyclic) (root : V) (j N : ℕ)
    (hj : 1 ≤ j) (e : Fin N ≃ (DistanceLayer G root j))
    (hd : ∀ v ∈ DistanceLayer G root j, G.degree v = 3) :
    Fin N × Fin 2 → (DistanceLayer G root (j + 1)) := fun b => by
  have hv := (Finset.mem_filter.mp (e b.1).property).2
  have hne : root ≠ (e b.1).val := by
    intro he
    rw [← he, dist_self] at hv
    omega
  have hc := actual_forest_forward_children_card_two hG hv.1 hne (hd _ (e b.1).property)
  let x := ChildCoordinate root (e b.1).val hc b.2
  have hx := actual_branch_child_member root (e b.1).val hc b.2
  exact ⟨x.val, by
    simp only [DistanceLayer, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hv.1.trans hx.1.reachable, by
      change G.dist root (ChildCoordinate root (e b.1).val hc b.2).val = j + 1
      rw [hx.2, hv.2]⟩⟩

theorem actual_successor_pair_map_adj (hG : G.IsAcyclic) (root : V) (j N : ℕ)
    (hj : 1 ≤ j) (e : Fin N ≃ (DistanceLayer G root j))
    (hd : ∀ v ∈ DistanceLayer G root j, G.degree v = 3) (b : Fin N × Fin 2) :
    G.Adj (e b.1).val (SuccessorPairMap hG root j N hj e hd b).val := by
  unfold SuccessorPairMap
  exact (actual_branch_child_member _ _ _ _).1

theorem actual_successor_pair_map_bijective (hG : G.IsAcyclic) (root : V) (j N : ℕ)
    (hj : 1 ≤ j) (e : Fin N ≃ (DistanceLayer G root j))
    (hd : ∀ v ∈ DistanceLayer G root j, G.degree v = 3) :
    Function.Bijective (SuccessorPairMap hG root j N hj e hd) := by
  constructor
  · intro a b heq
    have hae := (Finset.mem_filter.mp (e a.1).property).2
    have hbe := (Finset.mem_filter.mp (e b.1).property).2
    have hax := (Finset.mem_filter.mp (SuccessorPairMap hG root j N hj e hd a).property).2
    have hbx := (Finset.mem_filter.mp (SuccessorPairMap hG root j N hj e hd b).property).2
    have hxval := congrArg Subtype.val heq
    have hep : (e a.1).val = (e b.1).val := by
      apply actual_forest_parent_unique hG hax.1
        (actual_successor_pair_map_adj hG root j N hj e hd a).symm
      · rw [hxval]
        exact (actual_successor_pair_map_adj hG root j N hj e hd b).symm
      · omega
      · omega
    have hab : a.1 = b.1 := e.injective (Subtype.ext hep)
    rcases a with ⟨a0,a1⟩
    rcases b with ⟨b0,b1⟩
    dsimp at hab
    subst b0
    have hchild := hxval
    change (ChildCoordinate root (e a0).val _ a1).val =
      (ChildCoordinate root (e a0).val _ b1).val at hchild
    have ha1 : a1 = b1 := (ChildCoordinate root (e a0).val _).injective (Subtype.ext hchild)
    subst b1
    rfl
  · intro x
    have hx := (Finset.mem_filter.mp x.property).2
    have hne : root ≠ x.val := by
      intro he
      rw [← he, dist_self] at hx
      omega
    obtain ⟨v, hv, _⟩ := actual_forest_parent_exists hG hx.1 hne
    have hvj : v ∈ DistanceLayer G root j := by
      simp only [DistanceLayer, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hx.1.trans hv.1.reachable, by omega⟩
    let b0 := e.symm ⟨v,hvj⟩
    have hev : (e b0).val = v := by simp [b0]
    have hvr := (Finset.mem_filter.mp (e b0).property).2
    have hvne : root ≠ (e b0).val := by
      intro he
      rw [← he, dist_self] at hvr
      omega
    have hc := actual_forest_forward_children_card_two hG hvr.1 hvne (hd _ (e b0).property)
    have hxc : x.val ∈ ForwardChildren G root (e b0).val := by
      simp only [ForwardChildren, Finset.mem_filter, mem_neighborFinset]
      rw [hev]
      exact ⟨hv.1.symm, hv.2.symm⟩
    let b1 := (ChildCoordinate root (e b0).val hc).symm ⟨x.val,hxc⟩
    refine ⟨(b0,b1), Subtype.ext ?_⟩
    change (ChildCoordinate root (e b0).val _ b1).val = x.val
    simp [b1]

noncomputable def SuccessorCoordinate (hG : G.IsAcyclic) (root : V) (j N : ℕ)
    (hj : 1 ≤ j) (e : Fin N ≃ (DistanceLayer G root j))
    (hd : ∀ v ∈ DistanceLayer G root j, G.degree v = 3) :
    Fin (N * 2) ≃ (DistanceLayer G root (j + 1)) :=
  finProdFinEquiv.symm.trans (Equiv.ofBijective _
    (actual_successor_pair_map_bijective hG root j N hj e hd))

theorem actual_successor_coordinate_parent (hG : G.IsAcyclic) (root : V) (j N : ℕ)
    (hj : 1 ≤ j) (e : Fin N ≃ (DistanceLayer G root j))
    (hd : ∀ v ∈ DistanceLayer G root j, G.degree v = 3) (b : Fin (N * 2)) :
    G.Adj (e (finProdFinEquiv.symm b).1).val
      (SuccessorCoordinate hG root j N hj e hd b).val := by
  exact actual_successor_pair_map_adj hG root j N hj e hd (finProdFinEquiv.symm b)

end Reference.MD06RadiusEmbedding
