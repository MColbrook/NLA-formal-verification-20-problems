module

public import NLA.MD06.RadiusEmbedding.BoundaryGeometry

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open Reference.MD06CleanCycle
attribute [local instance] Classical.propDecidable

theorem actual_next_previous_root_ne {ell : ℕ} (hell : 4 ≤ ell) (i : Fin ell) :
    NextRoot i ≠ PreviousRoot i := by
  intro he
  have hi := i.isLt
  have hm : (i.val+1)%ell = (i.val+ell-1)%ell := congrArg Fin.val he
  by_cases h0 : i.val = 0
  · have hp : (i.val+ell-1)%ell = ell-1 := by
      rw [h0]
      simpa only [Nat.zero_add] using Nat.mod_eq_of_lt (show ell-1 < ell by omega)
    have hn : (i.val+1)%ell = 1 := by rw [h0]; exact Nat.mod_eq_of_lt (by omega)
    omega
  · have hp : (i.val+ell-1)%ell = i.val-1 := by
      have he : i.val+ell-1 = (i.val-1)+ell := by omega
      rw [he,Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hlast : i.val+1=ell
    · have hn : (i.val+1)%ell=0 := by rw [hlast,Nat.mod_self]
      omega
    · have hn : (i.val+1)%ell=i.val+1 := Nat.mod_eq_of_lt (by omega)
      omega

theorem actual_tree_node_zero_eq_root {ell R : ℕ} (x : TreeNodes ell R)
    (h0 : x.1.val = 0) : x = RootNode x.2.1 := by
  rcases x with ⟨j,i,b⟩
  have hj : j = 0 := Fin.ext h0
  subst j
  have hb : b = 0 := by
    apply Fin.ext
    have hbi := b.isLt
    change b.val < 1 at hbi
    change b.val = 0
    omega
  subst b
  rfl

theorem actual_tree_neighbors_card_interior {ell R : ℕ} (hell : 4 ≤ ell)
    (hR : 4 ≤ R) (x : TreeNodes ell R) (hx : x.1.val < R) :
    (TreeNeighbors hR x).card = 3 := by
  by_cases h0 : x.1.val = 0
  · have hab : RootNode (R := R) (NextRoot x.2.1) ≠ RootNode (PreviousRoot x.2.1) := by
      intro he
      exact actual_next_previous_root_ne hell _ (congrArg (fun z => z.2.1) he)
    have hac : RootNode (NextRoot x.2.1) ≠ ChildZero x hx := by
      intro he
      have hd := congrArg (fun z => z.1.val) he
      simp only [RootNode,ChildZero] at hd
      omega
    have hbc : RootNode (PreviousRoot x.2.1) ≠ ChildZero x hx := by
      intro he
      have hd := congrArg (fun z => z.1.val) he
      simp only [RootNode,ChildZero] at hd
      omega
    simp [TreeNeighbors,h0,hab,hac,hbc]
  · have hp : 0 < x.1.val := by omega
    have hab : ParentNode x hp ≠ ChildZero x hx := by
      intro he
      have hd := congrArg (fun z => z.1.val) he
      simp only [ParentNode,ChildZero] at hd
      omega
    have hac : ParentNode x hp ≠ ChildOne x hp hx := by
      intro he
      have hd := congrArg (fun z => z.1.val) he
      simp only [ParentNode,ChildOne] at hd
      omega
    have hbc : ChildZero x hx ≠ ChildOne x hp hx := by
      intro he
      have hd := congrArg (fun z => z.2.2.val) he
      simp only [ChildZero,ChildOne] at hd
      omega
    simp [TreeNeighbors,h0,hx,hab,hac,hbc]

end Reference.MD06RadiusEmbedding
