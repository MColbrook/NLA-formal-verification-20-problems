module

public import NLA.PF02.UniformPositiveOrientation.RationalDefinitions
public import NLA.PF02.UniformPositiveOrientation.Quotient
public import Mathlib.Data.Rat.Cast.Order

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02BlockConstruction Reference.PF02Normalization Set

theorem enumerated_integer_factor_cast (r : ℕ) (i : Fin (Fintype.card (BlockIndex r))) :
    (enumeratedIntegerFactor r i).map (Int.castRingHom ℝ) = enumeratedFactor r i :=
  finite_block_factor_int_cast r _

theorem enumerated_integer_factor_trace_cast (r : ℕ) (i : Fin (Fintype.card (BlockIndex r))) :
    (((enumeratedIntegerFactor r i).trace : ℤ) : ℝ) = (enumeratedFactor r i).trace := by
  have h := AddMonoidHom.map_trace (Int.castRingHom ℝ) (enumeratedIntegerFactor r i)
  rw [enumerated_integer_factor_cast] at h
  simpa only [Int.coe_castRingHom] using h

theorem rational_perturbed_gram_cast (r : ℕ) (q : ℚ) :
    (rationalPerturbedGram r q).map (Rat.castHom ℝ) = perturbedBlockGram r (q : ℝ) := by
  ext i j
  change ((rationalPerturbedGram r q i j : ℚ) : ℝ) = perturbedBlockGram r (q : ℝ) i j
  rw [perturbed_gram_entry_expansion]
  unfold rationalPerturbedGram
  push_cast
  rw [enumerated_integer_factor_trace_cast,enumerated_integer_factor_trace_cast]
  rfl

theorem all_size_positive_rational_disconnected_witness {k : ℕ} (hk : 3 ≤ k) :
    ∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℚ), N = k*(k+1)/2 ∧
      (∀ i j, 0 < M i j) ∧ (M.map (Rat.castHom ℝ)).rank = N ∧
      NLA.PF02.IsPSDRank (M.map (Rat.castHom ℝ)) k ∧
      ¬ IsConnected (Set.univ : Set (NLA.PF02.OrbitSpace (M.map (Rat.castHom ℝ)) k)) := by
  let r := k-3
  have he : k = 3+r := by dsimp [r]; omega
  obtain ⟨ε,hε,hall⟩ := actual_positive_perturbed_witness_near_zero r
  obtain ⟨q,hq0,hqε⟩ := exists_rat_btwn hε
  have hw := hall (q : ℝ) hq0 hqε
  refine ⟨Fintype.card (BlockIndex r),rationalPerturbedGram r q,?_,?_,?_,?_,?_⟩
  · rw [block_index_card,he]
    congr 2 <;> omega
  · intro i j
    have hp : 0 < ((rationalPerturbedGram r q i j : ℚ) : ℝ) := by
      change 0 < ((rationalPerturbedGram r q).map (Rat.castHom ℝ)) i j
      rw [rational_perturbed_gram_cast]
      exact hw.1 i j
    exact_mod_cast hp
  · rw [rational_perturbed_gram_cast,hw.2.1,block_index_card]
    congr 2 <;> omega
  · rw [rational_perturbed_gram_cast,he]
    exact hw.2.2.1
  · rw [rational_perturbed_gram_cast,he]
    exact hw.2.2.2

#print axioms enumerated_integer_factor_cast
#print axioms enumerated_integer_factor_trace_cast
#print axioms rational_perturbed_gram_cast
#print axioms all_size_positive_rational_disconnected_witness
end Reference.PF02UniformPositiveOrientation
