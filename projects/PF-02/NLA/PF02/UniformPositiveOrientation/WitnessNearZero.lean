module

public import NLA.PF02.UniformPositiveOrientation.WitnessDefinitions
public import NLA.PF02.UniformPositiveOrientation.WitnessNormalization

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization Set Filter
open scoped Topology BigOperators MatrixOrder

theorem continuous_leading_rows (r : ℕ) :
    Continuous (leadingRows (r := r) :
      (Fin (Fintype.card (BlockIndex r)) → Matrix (Fin (3+r)) (Fin (3+r)) ℝ) →
      NLA.PF02.Paper.SymIndex 3 → Matrix (Fin (3+r)) (Fin (3+r)) ℝ) := by
  unfold leadingRows Reference.PF02BlockSupportRecovery.blockRows
  fun_prop

theorem continuousOn_normalized_witness_product (r : ℕ) :
    ContinuousOn (normalizedWitnessProduct r) (Ici 0) := by
  let F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r) :=
    ⟨(enumeratedFactor r,enumeratedFactor r),enumerated_factorization r⟩
  let G : NLA.PF02.Factorization (enumeratedRealGram r) (3+r) :=
    ⟨(enumeratedReflectedFactor r,enumeratedReflectedFactor r),enumerated_reflected_factorization r⟩
  have hF : (rowSum (enumeratedFactor r)).PosDef :=
    actual_factor_row_sum_posDef _ (enumerated_real_gram_rank r) F
  have hG : (rowSum (enumeratedReflectedFactor r)).PosDef :=
    actual_factor_row_sum_posDef _ (enumerated_real_gram_rank r) G
  have hc : Continuous (fun A : Fin (Fintype.card (BlockIndex r)) → Matrix (Fin (3+r)) (Fin (3+r)) ℝ =>
      orientationPolynomial (leadingRows (r := r) A)) :=
    (continuous_orientation_polynomial (3+r)).comp (continuous_leading_rows r)
  have hca := hc.comp_continuousOn (continuousOn_shifted_normalization (enumeratedFactor r) hF)
  have hcb := hc.comp_continuousOn (continuousOn_shifted_normalization (enumeratedReflectedFactor r) hG)
  exact hca.mul hcb

theorem actual_normalized_witness_product_negative_near_zero (r : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ η : ℝ, 0 ≤ η → η < ε → normalizedWitnessProduct r η < 0 := by
  have hA : shiftedFactors (enumeratedFactor r) 0 = enumeratedFactor r := by
    funext i
    simp only [shiftedFactors,zero_smul,add_zero]
  have hB : shiftedFactors (enumeratedReflectedFactor r) 0 = enumeratedReflectedFactor r := by
    funext i
    simp only [shiftedFactors,zero_smul,add_zero]
  have hn : normalizedWitnessProduct r 0 < 0 := by
    unfold normalizedWitnessProduct
    rw [hA,hB]
    exact actual_zero_normalized_witness_product_negative r
  have he : {η : ℝ | normalizedWitnessProduct r η < 0} ∈ 𝓝[Ici 0] (0 : ℝ) :=
    (continuousOn_normalized_witness_product r 0 (by simp)).eventually (Iio_mem_nhds hn)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨ε,hε,?_⟩
  intro η hη hεη
  apply hball
  exact ⟨by simpa [Metric.mem_ball,Real.dist_eq,abs_of_nonneg hη] using hεη,hη⟩

#print axioms continuous_leading_rows
#print axioms continuousOn_normalized_witness_product
#print axioms actual_normalized_witness_product_negative_near_zero
end Reference.PF02UniformPositiveOrientation
