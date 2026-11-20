module

public import NLA.PF02.BlockConstruction.EnumeratedDefinitions
public import NLA.PF02.BlockConstruction.Integer
public import NLA.PF02.IntrinsicSupport.DimensionSupport

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockConstruction
open Matrix NLA.PF02.Paper Reference.PF02PositiveBasis Reference.PF02IntrinsicSupport
open scoped BigOperators MatrixOrder

theorem enumerated_integer_entry_nonneg (r : ℕ)
    (i j : Fin (Fintype.card (BlockIndex r))) : 0 ≤ enumeratedIntegerGram r i j :=
  finite_block_integer_entry_nonneg r _ _

theorem enumerated_real_gram_eq (r : ℕ) : enumeratedRealGram r =
    (finiteBlockGram r).reindex (Fintype.equivFin (BlockIndex r)) (Fintype.equivFin (BlockIndex r)) := by
  ext i j
  exact congrFun (congrFun (finite_block_gram_int_cast r)
    ((Fintype.equivFin (BlockIndex r)).symm i)) ((Fintype.equivFin (BlockIndex r)).symm j)

theorem enumerated_real_gram_rank (r : ℕ) :
    (enumeratedRealGram r).rank = (3+r)*(3+r+1)/2 := by
  rw [enumerated_real_gram_eq, Matrix.rank_reindex, finite_block_gram_rank]
  congr 2 <;> omega

theorem enumerated_factorization (r : ℕ) :
    NLA.PF02.IsFactorization (enumeratedRealGram r) (enumeratedFactor r, enumeratedFactor r) := by
  refine ⟨fun i => finite_block_factor_posSemidef r _, fun j => finite_block_factor_posSemidef r _, ?_⟩
  intro i j
  rw [enumerated_real_gram_eq]
  rfl

theorem enumerated_psd_rank (r : ℕ) : NLA.PF02.IsPSDRank (enumeratedRealGram r) (3+r) := by
  constructor
  · exact ⟨by omega, ⟨⟨(enumeratedFactor r, enumeratedFactor r), enumerated_factorization r⟩⟩⟩
  · intro l hl
    rcases hl with ⟨_, ⟨F⟩⟩
    have hb := NLA.PF02.Paper.factorization_symmetric_rank_le F
    rw [enumerated_real_gram_rank] at hb
    exact triangular_rank_dimension_le hb

theorem all_size_integer_witness {k : ℕ} (hk : 3 ≤ k) :
    ∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℤ), N = k*(k+1)/2 ∧
      (∀ i j, 0 ≤ M i j) ∧ (M.map (Int.castRingHom ℝ)).rank = N ∧
      NLA.PF02.IsPSDRank (M.map (Int.castRingHom ℝ)) k := by
  let r := k-3
  have he : k = 3+r := by dsimp [r]; omega
  refine ⟨Fintype.card (BlockIndex r), enumeratedIntegerGram r, ?_,
    enumerated_integer_entry_nonneg r, ?_, ?_⟩
  · rw [block_index_card, he]
    congr 2 <;> omega
  · change (enumeratedRealGram r).rank = Fintype.card (BlockIndex r)
    rw [enumerated_real_gram_rank, block_index_card]
    congr 2 <;> omega
  · change NLA.PF02.IsPSDRank (enumeratedRealGram r) k
    rw [he]
    exact enumerated_psd_rank r

#print axioms all_size_integer_witness
#print axioms enumerated_integer_entry_nonneg
#print axioms enumerated_real_gram_eq
#print axioms enumerated_real_gram_rank
#print axioms enumerated_factorization
#print axioms enumerated_psd_rank
end Reference.PF02BlockConstruction
