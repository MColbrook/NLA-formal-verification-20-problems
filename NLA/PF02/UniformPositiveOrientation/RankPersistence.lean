module

public import NLA.PF02.UniformPositiveOrientation.Uniform

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction NLA.PF02.Paper
open scoped Topology

theorem square_det_ne_zero_of_full_rank {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hR : M.rank = n) : M.det ≠ 0 := by
  have hi : LinearIndependent ℝ M.row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Set.finrank,← Matrix.rank_eq_finrank_span_row,hR,Fintype.card_fin]
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hi)

theorem actual_perturbed_block_full_rank_near_zero (r : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : ℝ, |η| < ε →
      (perturbedBlockGram r η).rank = (3+r)*(3+r+1)/2 := by
  have hN : Fintype.card (BlockIndex r) = (3+r)*(3+r+1)/2 := by
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using block_index_card r
  have hR : (perturbedBlockGram r 0).rank = Fintype.card (BlockIndex r) := by
    rw [perturbed_block_gram_zero,enumerated_real_gram_rank,hN]
  have h0 := square_det_ne_zero_of_full_rank (perturbedBlockGram r 0) hR
  have hc : Continuous (fun η => (perturbedBlockGram r η).det) :=
    (continuous_perturbed_block_gram r).matrix_det
  have ho : IsOpen {η : ℝ | (perturbedBlockGram r η).det ≠ 0} := isOpen_ne.preimage hc
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds h0)
  refine ⟨ε,hε,?_⟩
  intro η hη
  have hn : (perturbedBlockGram r η).det ≠ 0 :=
    hball (by simpa [Metric.mem_ball,Real.dist_eq] using hη)
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hn)),
    Fintype.card_fin,hN]

#print axioms square_det_ne_zero_of_full_rank
#print axioms actual_perturbed_block_full_rank_near_zero
end Reference.PF02UniformPositiveOrientation
