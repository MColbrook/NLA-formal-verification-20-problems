module

public import NLA.PF02.GlobalOrientation.IntegerAllSize
public import NLA.PF02.UniformPositiveOrientation.RationalWitness
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.PF02UniformPositiveOrientation
open Matrix
theorem paper_all_size_disconnected_witness {k : ℕ} (hk : 3 ≤ k) :
  (∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℤ),
      N = k*(k+1)/2 ∧ (∀ i j, 0 ≤ M i j) ∧
      (M.map (Int.castRingHom ℝ)).rank = N ∧ NLA.PF02.IsPSDRank (M.map (Int.castRingHom ℝ)) k ∧
      ¬ IsConnected (Set.univ : Set (NLA.PF02.OrbitSpace (M.map (Int.castRingHom ℝ)) k))) ∧
  (∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℚ), N = k*(k+1)/2 ∧
      (∀ i j, 0 < M i j) ∧ (M.map (Rat.castHom ℝ)).rank = N ∧
      NLA.PF02.IsPSDRank (M.map (Rat.castHom ℝ)) k ∧
      ¬ IsConnected (Set.univ : Set (NLA.PF02.OrbitSpace (M.map (Rat.castHom ℝ)) k))) :=
  ⟨Reference.PF02GlobalOrientation.all_size_integer_disconnected_witness hk,
    all_size_positive_rational_disconnected_witness hk⟩
#print axioms paper_all_size_disconnected_witness
end Reference.PF02UniformPositiveOrientation
