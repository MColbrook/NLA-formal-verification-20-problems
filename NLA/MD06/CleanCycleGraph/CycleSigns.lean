module

public import NLA.MD06.CleanCycleGraph.TopologyDefinitions
public import NLA.MD06.CleanCycleGraph.LevelCounts

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open Reference.MD06CycleProfile

theorem actual_next_root_residue {ell : ℕ} (hdiv : 4 ∣ ell) (i : Fin ell) :
    (NextRoot i).val%4 = (i.val+1)%4 := by
  exact Nat.mod_mod_of_dvd _ hdiv

theorem actual_previous_root_residue {ell : ℕ} (hell : 4 ≤ ell) (hdiv : 4 ∣ ell) (i : Fin ell) :
    (PreviousRoot i).val%4 = if i.val = 0 then 3 else (i.val-1)%4 := by
  have hm : ell%4 = 0 := Nat.mod_eq_zero_of_dvd hdiv
  change ((i.val+ell-1)%ell)%4 = _
  rw [Nat.mod_mod_of_dvd _ hdiv]
  by_cases hi : i.val = 0
  · simp [hi]
    omega
  · rw [if_neg hi]
    have he : i.val+ell-1 = (i.val-1)+ell := by omega
    rw [he,Nat.add_mod,hm,Nat.add_zero,Nat.mod_mod]

theorem actual_cycle_neighbor_signs_opposite {ell : ℕ} (hell : 4 ≤ ell) (hdiv : 4 ∣ ell) (i : Fin ell) :
    RootSign (NextRoot i) + RootSign (PreviousRoot i) = 0 := by
  unfold RootSign
  rw [actual_next_root_residue hdiv,actual_previous_root_residue hell hdiv]
  split_ifs <;> norm_num
  all_goals omega

theorem actual_cycle_two_neighbor_force {ell R : ℕ} (hell : 4 ≤ ell) (hdiv : 4 ∣ ell)
    (hR : 4 ≤ R) (i : Fin ell) :
    Real.sin (NodeProfile (RootNode (R := R) i)-NodeProfile (RootNode (R := R) (NextRoot i))) +
      Real.sin (NodeProfile (RootNode (R := R) i)-NodeProfile (RootNode (R := R) (PreviousRoot i))) =
      -RootSign i * Root R := by
  have hs := actual_cycle_neighbor_signs_opposite hell hdiv i
  have he : RootSign (PreviousRoot i) = -RootSign (NextRoot i) := by linarith
  simp only [NodeProfile,RootNode]
  rw [he]
  have hsin := actual_opposite_root_sine hR
  have hsinp : Real.sin (Height R (Root R) 0*2) = -Root R := by simpa [mul_comm] using hsin
  unfold RootSign
  split_ifs <;> ring_nf
  all_goals simp [hsinp]
end Reference.MD06CleanCycle
