module

public import NLA.MD06.CleanRadiusCardinality.Excess
public import NLA.MD06.RadiusEmbedding.PaperLayers

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Reference.MD06CleanRadiusCardinality
open SimpleGraph
open Reference.MD06RadiusEmbedding
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem actual_outside_neighbors_degree (S : Set V) (x : S) :
    (G.neighborFinset x.val \ S.toFinset).card + (G.induce S).degree x =
      G.degree x.val := by
  have hd := congrArg Finset.card (map_neighborFinset_induce (G := G) x)
  simp only [Finset.card_map, card_neighborFinset_eq_degree] at hd
  have hs := Finset.card_sdiff_add_card_inter (G.neighborFinset x.val) S.toFinset
  rw [← hd] at hs
  simpa only [card_neighborFinset_eq_degree] using hs

theorem actual_outside_neighbors_card_bound (S : Set V)
    (hcubic : ∀ x : V, G.degree x = 3)
    (hedges : S.toFinset.card ≤ (G.induce S).edgeFinset.card) :
    (∑ x ∈ S.toFinset, (G.neighborFinset x \ S.toFinset).card) ≤ S.toFinset.card := by
  have hsum :
      (∑ x ∈ S.toFinset, (G.neighborFinset x \ S.toFinset).card) =
      ∑ x : S, (G.neighborFinset x.val \ S.toFinset).card := by
    apply Finset.sum_bij (fun x hx => (⟨x, Set.mem_toFinset.mp hx⟩ : S))
    · intro x hx; simp
    · intro x hx y hy hxy
      exact congrArg Subtype.val hxy
    · intro x hx
      exact ⟨x.val, Set.mem_toFinset.mpr x.prop, rfl⟩
    · intro x hx; rfl
  have hdegrees := (G.induce S).sum_degrees_eq_twice_card_edges
  have htotal :
      (∑ x : S, (G.neighborFinset x.val \ S.toFinset).card) +
        2 * (G.induce S).edgeFinset.card = 3 * S.toFinset.card := by
    calc
      _ = ∑ x : S, ((G.neighborFinset x.val \ S.toFinset).card +
          (G.induce S).degree x) := by
        rw [Finset.sum_add_distrib, hdegrees]
      _ = ∑ _x : S, 3 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [actual_outside_neighbors_degree S x, hcubic x.val]
      _ = 3 * S.toFinset.card := by simp [Nat.mul_comm]
  rw [hsum]
  omega

theorem actual_radius_successor_subset {v : V} (c : G.Walk v v) (R : ℕ) :
    (CycleRadius G c (R + 1)).toFinset ⊆
      (CycleRadius G c R).toFinset ∪
        (CycleRadius G c R).toFinset.biUnion
          (fun x => G.neighborFinset x \ (CycleRadius G c R).toFinset) := by
  intro y hy
  by_cases hyR : y ∈ CycleRadius G c R
  · exact Finset.mem_union_left _ (Set.mem_toFinset.mpr hyR)
  · apply Finset.mem_union_right
    obtain ⟨u, hu, hyu, hdist⟩ := Set.mem_toFinset.mp hy
    obtain ⟨p, hp, hlen⟩ := hyu.exists_path_of_dist
    cases p with
    | nil =>
        exact False.elim (hyR ⟨y, hu, Reachable.refl _, by simp⟩)
    | @cons y x u hxy tail =>
        have htail : tail.length ≤ R := by
          simp only [Walk.length_cons] at hlen
          omega
        have hx : x ∈ CycleRadius G c R :=
          ⟨u, hu, tail.reachable, (SimpleGraph.dist_le tail).trans htail⟩
        exact Finset.mem_biUnion.mpr ⟨x, Set.mem_toFinset.mpr hx,
          Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset x y).mpr hxy.symm,
            fun hm => hyR (Set.mem_toFinset.mp hm)⟩⟩

theorem actual_radius_card_doubles {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    (hcubic : ∀ x : V, G.degree x = 3) (R : ℕ) :
    (CycleRadius G c (R + 1)).toFinset.card ≤
      2 * (CycleRadius G c R).toFinset.card := by
  let S := (CycleRadius G c R).toFinset
  have he : (CycleRadius G c R).toFinset.card ≤
      (G.induce (CycleRadius G c R)).edgeFinset.card := by
    have h := actual_connected_cycle_card (LiftedCycle c R)
      (actual_lifted_cycle_isCycle c R hc) (actual_cycle_radius_induced_connected c R)
    simpa only [Set.toFinset_card] using h
  have ho := actual_outside_neighbors_card_bound (CycleRadius G c R) hcubic he
  have hb : (S.biUnion (fun x => G.neighborFinset x \ S)).card ≤
      ∑ x ∈ S, (G.neighborFinset x \ S).card := Finset.card_biUnion_le
  have hu := Finset.card_union_le S (S.biUnion (fun x => G.neighborFinset x \ S))
  have hs := Finset.card_le_card (actual_radius_successor_subset c R)
  change (∑ x ∈ S, (G.neighborFinset x \ S).card) ≤ S.card at ho
  change (CycleRadius G c (R + 1)).toFinset.card ≤ 2 * S.card
  change (CycleRadius G c (R + 1)).toFinset.card ≤
    (S ∪ S.biUnion (fun x => G.neighborFinset x \ S)).card at hs
  omega

theorem actual_radius_zero_finset {v : V} (c : G.Walk v v) :
    (CycleRadius G c 0).toFinset = c.support.toFinset := by
  ext x
  simp only [Set.mem_toFinset, List.mem_toFinset, CycleRadius, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨u, hu, hxu, hd⟩
    have he : x = u := hxu.dist_eq_zero_iff.mp (by omega)
    simpa only [he] using hu
  · intro hx
    exact ⟨x, hx, Reachable.refl _, by simp⟩

theorem actual_cycle_radius_card_bound {v : V} (c : G.Walk v v) (hc : c.IsCycle)
    (hcubic : ∀ x : V, G.degree x = 3) (R : ℕ) :
    Fintype.card (CycleRadius G c R) ≤ c.length * 2 ^ R := by
  have hb : (CycleRadius G c R).toFinset.card ≤ c.length * 2 ^ R := by
    induction R with
    | zero =>
        rw [actual_radius_zero_finset, actual_cycle_support_card_length c hc]
        simp
    | succ R ih =>
        calc
          _ ≤ 2 * (CycleRadius G c R).toFinset.card := actual_radius_card_doubles c hc hcubic R
          _ ≤ 2 * (c.length * 2 ^ R) := Nat.mul_le_mul_left _ ih
          _ = c.length * 2 ^ (R + 1) := by rw [Nat.pow_succ]; ac_rfl
  simpa only [Set.toFinset_card] using hb

#print axioms actual_outside_neighbors_degree
#print axioms actual_outside_neighbors_card_bound
#print axioms actual_radius_successor_subset
#print axioms actual_radius_card_doubles
#print axioms actual_radius_zero_finset
#print axioms actual_cycle_radius_card_bound

end Reference.MD06CleanRadiusCardinality
