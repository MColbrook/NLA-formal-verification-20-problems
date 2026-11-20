module

public import NLA.MD06.CleanCycleGraph.Definitions
public import Mathlib.Logic.Function.Basic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06Correction
attribute [local instance] Classical.propDecidable

def RootNode {ell R : ℕ} (i : Fin ell) : TreeNodes ell R :=
  ⟨⟨0,by omega⟩,i,⟨0,by simp⟩⟩

def NextRoot {ell : ℕ} (i : Fin ell) : Fin ell :=
  ⟨(i.val+1)%ell,Nat.mod_lt _ (by have hi := i.isLt; omega)⟩

def PreviousRoot {ell : ℕ} (i : Fin ell) : Fin ell :=
  ⟨(i.val+ell-1)%ell,Nat.mod_lt _ (by have hi := i.isLt; omega)⟩

theorem parent_index_lt {j b : ℕ} (hj : 0 < j) (hb : b < 2^(j-1)) :
    b/2 < 2^(j-1-1) := by
  by_cases heq : j = 1
  · subst j
    norm_num at hb ⊢
    omega
  · have he : j-1 = (j-1-1)+1 := by omega
    have hp : 2^(j-1) = 2*2^(j-1-1) := by
      conv_lhs => rw [he,Nat.pow_succ]
      omega
    rw [hp] at hb
    omega

theorem child_zero_index_lt {j b : ℕ} (hb : b < 2^(j-1)) : 2*b < 2^j := by
  by_cases heq : j = 0
  · subst j
    norm_num at hb ⊢
    omega
  · have he : j = (j-1)+1 := by omega
    have hp : 2^j = 2*2^(j-1) := by
      conv_lhs => rw [he,Nat.pow_succ]
      omega
    rw [hp]
    omega

theorem child_one_index_lt {j b : ℕ} (hj : 0 < j) (hb : b < 2^(j-1)) : 2*b+1 < 2^j := by
  have he : j = (j-1)+1 := by omega
  have hp : 2^j = 2*2^(j-1) := by
    conv_lhs => rw [he,Nat.pow_succ]
    omega
  rw [hp]
  omega

def ParentNode {ell R : ℕ} (x : TreeNodes ell R) (hx : 0 < x.1.val) : TreeNodes ell R :=
  ⟨⟨x.1.val-1,by have h := x.1.isLt; omega⟩,x.2.1,
    ⟨x.2.2.val/2,parent_index_lt hx x.2.2.isLt⟩⟩

def ChildZero {ell R : ℕ} (x : TreeNodes ell R) (hx : x.1.val < R) : TreeNodes ell R :=
  ⟨⟨x.1.val+1,by omega⟩,x.2.1,
    ⟨2*x.2.2.val,by simpa using child_zero_index_lt x.2.2.isLt⟩⟩

def ChildOne {ell R : ℕ} (x : TreeNodes ell R) (h0 : 0 < x.1.val)
    (hx : x.1.val < R) : TreeNodes ell R :=
  ⟨⟨x.1.val+1,by omega⟩,x.2.1,
    ⟨2*x.2.2.val+1,by simpa using child_one_index_lt h0 x.2.2.isLt⟩⟩

def TreeNeighbors {ell R : ℕ} (hR : 4 ≤ R) (x : TreeNodes ell R) : Finset (TreeNodes ell R) := by
  classical
  exact if h0 : x.1.val = 0 then
    {RootNode (NextRoot x.2.1),RootNode (PreviousRoot x.2.1),ChildZero x (by omega)}
  else if hx : x.1.val < R then
    {ParentNode x (by omega),ChildZero x hx,ChildOne x (by omega) hx}
  else {ParentNode x (by omega)}

structure CleanCycleEmbedding {n ell R : ℕ} (G : SimpleGraph (Fin n)) (hR : 4 ≤ R) where
  nodes : TreeNodes ell R ↪ Fin n
  induced_neighbors : ∀ x, G.neighborFinset (nodes x) ∩ Finset.univ.image nodes =
    (TreeNeighbors hR x).image nodes
  closed_interior : ∀ x, x.1.val < R → G.neighborFinset (nodes x) ⊆ Finset.univ.image nodes

def EmbeddedProfile {n ell R : ℕ} (e : TreeNodes ell R ↪ Fin n) : Configuration n :=
  WithLp.toLp 2 (Function.extend e NodeProfile (fun _ => 0))
end Reference.MD06CleanCycle
