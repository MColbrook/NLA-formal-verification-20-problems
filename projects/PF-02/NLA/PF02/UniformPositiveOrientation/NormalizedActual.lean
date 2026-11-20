module

public import NLA.PF02.UniformPositiveOrientation.RegularDefinitions
public import NLA.PF02.UniformPositiveOrientation.RankPersistence
public import NLA.PF02.UniformPositiveOrientation.Covariance
public import NLA.PF02.Normalization.Process
public import NLA.PF02.Normalization.FullRank

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction
open Reference.PF02Normalization Reference.PF02JointCompactness Set Filter
open scoped BigOperators Topology MatrixOrder

theorem actual_regular_parameter_near_zero (r : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : ℝ, |η| < ε → regularParameter r η := by
  obtain ⟨a,ha,hA⟩ := actual_perturbed_block_full_rank_near_zero r
  obtain ⟨b,hb,hB⟩ := actual_uniform_normalized_orientation_product_pos r
  refine ⟨min a b,lt_min ha hb,?_⟩
  intro η hη
  exact ⟨hA η (lt_of_lt_of_le hη (min_le_left _ _)),
    hB η (lt_of_lt_of_le hη (min_le_right _ _))⟩

theorem actual_factor_row_sum_posDef {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (hR : M.rank = k*(k+1)/2)
    (F : NLA.PF02.Factorization M k) : (rowSum F.val.1).PosDef :=
  row_sum_posDef_of_full_trace_rank M F.val.1 F.val.2 F.property.1 F.property.2.2 hR

theorem actual_normalization_mem {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ) (hR : M.rank = k*(k+1)/2)
    (F : NLA.PF02.Factorization M k) :
    (normalizedRow F.val.1, normalizedColumn F.val.1 F.val.2) ∈ normalizedFactorSet (k := k) M := by
  have hs : (rowSum F.val.1).PosDef := actual_factor_row_sum_posDef M hR F
  exact ⟨normalized_row_posSemidef F.val.1 F.property.1,
    normalized_column_posSemidef F.val.1 F.val.2 F.property.2.1,
    normalized_row_sum F.val.1 F.property.1 hs,
    fun i j => (normalized_trace_pairing F.val.1 F.val.2 hs i j).trans (F.property.2.2 i j)⟩

theorem actual_normalized_orientation_ne_zero {r : ℕ} {η : ℝ} (h : regularParameter r η)
    (F : NLA.PF02.Factorization (perturbedBlockGram r η) (3+r)) :
    orientationPolynomial (leadingRows (r := r) (normalizedRow F.val.1)) ≠ 0 := by
  have hm := actual_normalization_mem (perturbedBlockGram r η) h.1 F
  have hI : (1 : Matrix (Fin (3+r)) (Fin (3+r)) ℝ) ∈ orthogonalSet (3+r) := by
    simp [orthogonalSet]
  have hp : 0 < normalizedOrientationProduct (r := r)
      (normalizedRow F.val.1,normalizedColumn F.val.1 F.val.2) 1 := h.2 _ hm 1 hI
  intro hz
  simp only [normalizedOrientationProduct,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one,hz,
    zero_mul] at hp
  exact lt_irrefl 0 hp

theorem actual_normalized_fiber_sign_congruent {r : ℕ} {η : ℝ} (h : regularParameter r η)
    (F G : NLA.PF02.Factorization (perturbedBlockGram r η) (3+r))
    (hFG : NLA.PF02.Congruent F G) : normalizedFiberSign F = normalizedFiberSign G := by
  obtain ⟨S,hRows,_⟩ := hFG
  let O : Matrix (Fin (3+r)) (Fin (3+r)) ℝ := normalizingCongruence F.val.1 G.val.1 S
  have hFP : (rowSum F.val.1).PosDef := actual_factor_row_sum_posDef _ h.1 F
  have hGP : (rowSum G.val.1).PosDef := actual_factor_row_sum_posDef _ h.1 G
  have hO : O ∈ orthogonalSet (3+r) :=
    normalizing_congruence_orthogonal F.val.1 G.val.1 F.property.1 G.property.1 hGP S hRows
  have hm := actual_normalization_mem (perturbedBlockGram r η) h.1 F
  have hp : 0 < normalizedOrientationProduct (r := r)
      (normalizedRow F.val.1,normalizedColumn F.val.1 F.val.2) O := h.2 _ hm O hO
  have he : leadingRows (r := r) (normalizedRow G.val.1) =
      fun p => O.transpose * leadingRows (r := r) (normalizedRow F.val.1) p * O := by
    funext p
    exact normalized_row_congruence F.val.1 G.val.1 hFP S hRows
      (Fintype.equivFin (BlockIndex r) (Sum.inl p))
  change 0 < orientationPolynomial (leadingRows (r := r) (normalizedRow F.val.1)) *
    orientationPolynomial (fun p => O.transpose * leadingRows (r := r) (normalizedRow F.val.1) p * O) at hp
  rw [← he] at hp
  rcases mul_pos_iff.mp hp with ⟨hf,hg⟩ | ⟨hf,hg⟩
  · simp [normalizedFiberSign,hf,hg]
  · simp [normalizedFiberSign,not_lt_of_gt hf,not_lt_of_gt hg]

#print axioms actual_regular_parameter_near_zero
#print axioms actual_factor_row_sum_posDef
#print axioms actual_normalization_mem
#print axioms actual_normalized_orientation_ne_zero
#print axioms actual_normalized_fiber_sign_congruent
end Reference.PF02UniformPositiveOrientation
