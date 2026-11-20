module

public import NLA.PF02.GlobalOrientation.Topology

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix Reference.PF02BlockConstruction

theorem all_size_integer_disconnected_witness {k : ℕ} (hk : 3 ≤ k) :
    ∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℤ),
      N = k*(k+1)/2 ∧ (∀ i j, 0 ≤ M i j) ∧
      (M.map (Int.castRingHom ℝ)).rank = N ∧ NLA.PF02.IsPSDRank (M.map (Int.castRingHom ℝ)) k ∧
      ¬ IsConnected (Set.univ : Set (NLA.PF02.OrbitSpace (M.map (Int.castRingHom ℝ)) k)) := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hk
  have hN : Fintype.card (BlockIndex r) = (3+r)*(3+r+1)/2 := by
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using block_index_card r
  refine ⟨Fintype.card (BlockIndex r),enumeratedIntegerGram r,hN,
    enumerated_integer_entry_nonneg r,?_,enumerated_psd_rank r,actual_all_size_orbit_quotient_disconnected r⟩
  change (enumeratedRealGram r).rank = Fintype.card (BlockIndex r)
  rw [enumerated_real_gram_rank,hN]

#print axioms all_size_integer_disconnected_witness
end Reference.PF02GlobalOrientation
