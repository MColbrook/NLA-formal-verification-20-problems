module

public import NLA.PF02.UniformPositiveOrientation.PerturbationFactors
public import NLA.PF02.UniformPositiveOrientation.NormalizedActual

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization
open Reference.PF02IntrinsicSupport
open scoped BigOperators MatrixOrder

theorem perturbed_gram_entry_expansion (r : ℕ) (η : ℝ)
    (i j : Fin (Fintype.card (BlockIndex r))) :
    perturbedBlockGram r η i j = enumeratedRealGram r i j +
      η * (enumeratedFactor r i).trace + η * (enumeratedFactor r j).trace + η^2 * (3+r) := by
  have he : Matrix.trace (enumeratedFactor r i * enumeratedFactor r j) = enumeratedRealGram r i j :=
    (enumerated_factorization r).2.2 i j
  simp only [perturbedBlockGram,Reference.PF02JointCompactness.perturbedGram,
    mul_add,add_mul,Matrix.trace_add,smul_mul_assoc,mul_smul_comm,Matrix.trace_smul,
    Matrix.mul_one,Matrix.one_mul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul,he]
  push_cast
  ring

theorem actual_perturbed_gram_entries_positive (r : ℕ) (η : ℝ) (hη : 0 < η)
    (i j : Fin (Fintype.card (BlockIndex r))) : 0 < perturbedBlockGram r η i j := by
  rw [perturbed_gram_entry_expansion]
  have h0 : 0 ≤ enumeratedRealGram r i j := by
    change 0 ≤ ((enumeratedIntegerGram r i j : ℤ) : ℝ)
    exact_mod_cast enumerated_integer_entry_nonneg r i j
  have hi : 0 ≤ η * (enumeratedFactor r i).trace :=
    mul_nonneg hη.le ((enumerated_factorization r).1 i).trace_nonneg
  have hj : 0 ≤ η * (enumeratedFactor r j).trace :=
    mul_nonneg hη.le ((enumerated_factorization r).1 j).trace_nonneg
  have hk : 0 < η^2 * (3+r : ℝ) := mul_pos (sq_pos_of_pos hη) (by positivity)
  linarith

theorem actual_perturbed_psd_rank {r : ℕ} {η : ℝ} (h : regularParameter r η) (hη : 0 ≤ η) :
    NLA.PF02.IsPSDRank (perturbedBlockGram r η) (3+r) := by
  constructor
  · exact ⟨by omega,⟨⟨(shiftedFactors (enumeratedFactor r) η,shiftedFactors (enumeratedFactor r) η),
      actual_shifted_factorization r η hη⟩⟩⟩
  · intro l hl
    rcases hl with ⟨_,⟨F⟩⟩
    have hb := NLA.PF02.Paper.factorization_symmetric_rank_le F
    rw [h.1] at hb
    exact triangular_rank_dimension_le hb

#print axioms perturbed_gram_entry_expansion
#print axioms actual_perturbed_gram_entries_positive
#print axioms actual_perturbed_psd_rank
end Reference.PF02UniformPositiveOrientation
