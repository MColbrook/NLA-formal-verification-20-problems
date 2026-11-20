module

public import NLA.PF02.UniformPositiveOrientation.CompactPositive
public import NLA.PF02.UniformPositiveOrientation.OrthogonalCompactness
public import NLA.PF02.GlobalOrientation.Topology
public import NLA.PF02.JointCompactness.Compactness

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction
open Reference.PF02Normalization Reference.PF02JointCompactness Set Filter
open scoped BigOperators Topology MatrixOrder

theorem perturbed_block_gram_zero (r : ℕ) : perturbedBlockGram r 0 = enumeratedRealGram r := by
  ext i j
  simpa [perturbedBlockGram,perturbedGram] using (enumerated_factorization r).2.2 i j

theorem continuous_perturbed_block_gram (r : ℕ) : Continuous (perturbedBlockGram r) :=
  continuous_perturbed_gram (enumeratedFactor r)

theorem continuous_normalized_orientation_product (r : ℕ) :
    Continuous (fun Z : FactorPair (Fintype.card (BlockIndex r)) (Fintype.card (BlockIndex r)) (3+r) ×
      Matrix (Fin (3+r)) (Fin (3+r)) ℝ => normalizedOrientationProduct (r := r) Z.1 Z.2) := by
  unfold normalizedOrientationProduct
  apply Continuous.mul
  · apply (continuous_orientation_polynomial (3+r)).comp
    unfold leadingRows Reference.PF02BlockSupportRecovery.blockRows
    fun_prop
  · apply (continuous_orientation_polynomial (3+r)).comp
    unfold leadingRows Reference.PF02BlockSupportRecovery.blockRows
    fun_prop

theorem actual_uniform_normalized_orientation_product_pos (r : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : ℝ, |η| < ε →
      ∀ F : FactorPair (Fintype.card (BlockIndex r)) (Fintype.card (BlockIndex r)) (3+r),
      F ∈ normalizedFactorSet (k := 3+r) (perturbedBlockGram r η) →
      ∀ O : Matrix (Fin (3+r)) (Fin (3+r)) ℝ, O ∈ orthogonalSet (3+r) →
        0 < normalizedOrientationProduct (r := r) F O := by
  classical
  have hzero : ∀ F : FactorPair (Fintype.card (BlockIndex r)) (Fintype.card (BlockIndex r)) (3+r),
      (0,F) ∈ jointNormalizedFactorSet (k := 3+r) (perturbedBlockGram r) (-1) 1 →
      ∀ O : Matrix (Fin (3+r)) (Fin (3+r)) ℝ, O ∈ orthogonalSet (3+r) →
        0 < normalizedOrientationProduct (r := r) F O := by
    intro F hF O hO
    have hactual : F ∈ normalizedFactorSet (k := 3+r) (enumeratedRealGram r) := by
      simpa only [perturbed_block_gram_zero] using hF.2
    let FF : NLA.PF02.Factorization (enumeratedRealGram r) (3+r) :=
      ⟨F,⟨hactual.1,hactual.2.1,hactual.2.2.2⟩⟩
    exact actual_orthogonal_orientation_product_pos FF O hO
  obtain ⟨ε,hε,hall⟩ := compact_parameter_positive
    (jointNormalizedFactorSet (k := 3+r) (perturbedBlockGram r) (-1) 1)
    (orthogonalSet (3+r))
    (joint_normalized_factor_set_isCompact (perturbedBlockGram r)
      (continuous_perturbed_block_gram r) (-1) 1)
    (orthogonal_set_isCompact (3+r))
    (fun Z : FactorPair (Fintype.card (BlockIndex r)) (Fintype.card (BlockIndex r)) (3+r) ×
      Matrix (Fin (3+r)) (Fin (3+r)) ℝ => normalizedOrientationProduct (r := r) Z.1 Z.2)
    (continuous_normalized_orientation_product r) hzero
  refine ⟨min ε 1,lt_min hε (by norm_num),?_⟩
  intro η hη F hF O hO
  have hεη : |η| < ε := lt_of_lt_of_le hη (min_le_left _ _)
  have h1η : |η| < 1 := lt_of_lt_of_le hη (min_le_right _ _)
  exact hall η hεη F ⟨abs_le.mp h1η.le,hF⟩ O hO

#print axioms perturbed_block_gram_zero
#print axioms continuous_perturbed_block_gram
#print axioms continuous_normalized_orientation_product
#print axioms actual_uniform_normalized_orientation_product_pos
end Reference.PF02UniformPositiveOrientation
