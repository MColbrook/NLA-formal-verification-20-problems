module

public import NLA.MD06.QuantitativeCorrection.MeanZeroLaplacian
public import NLA.MD06.QuantitativeCorrection.CompactBall

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open Set
open scoped BigOperators Topology
open Reference.MD06Actual

theorem actual_laplacian_euclidean_quadratic_continuous {n : ℕ} (G : SimpleGraph (Fin n)) :
    Continuous (fun z : Configuration n => LaplacianQuadratic G (fun i => z i)) := by
  classical
  unfold LaplacianQuadratic
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  split_ifs
  · fun_prop
  · exact continuous_const

theorem actual_laplacian_euclidean_quadratic_smul {n : ℕ} (G : SimpleGraph (Fin n))
    (z : Configuration n) (a : ℝ) :
    LaplacianQuadratic G (fun i => (a • z) i) = a^2 * LaplacianQuadratic G (fun i => z i) := by
  classical
  unfold LaplacianQuadratic
  simp only [Finset.mul_sum,PiLp.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs
  · ring
  · ring

theorem actual_mean_zero_unit_sphere_compact (n : ℕ) :
    IsCompact {z : Configuration n | (∑ i, z i) = 0 ∧ ‖z‖ = 1} := by
  have hz : IsClosed {z : Configuration n | (∑ i, z i) = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have he : {z : Configuration n | (∑ i, z i) = 0 ∧ ‖z‖ = 1} =
      Metric.sphere (0 : Configuration n) 1 ∩ {z | (∑ i, z i) = 0} := by
    ext z
    simp only [Set.mem_ofPred,Set.mem_inter_iff,Metric.mem_sphere,dist_zero_right,and_comm]
  rw [he]
  exact (isCompact_sphere (0 : Configuration n) 1).inter_right hz

theorem actual_connected_euclidean_poincare_exists {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ z : Configuration n, (∑ i, z i) = 0 →
      gamma * ‖z‖^2 ≤ LaplacianQuadratic G (fun i => z i) := by
  classical
  let S : Set (Configuration n) := {z | (∑ i, z i) = 0 ∧ ‖z‖ = 1}
  have hu : ∀ z : Configuration n, (∑ i, z i) = 0 → z ≠ 0 →
      (‖z‖⁻¹ • z) ∈ S := by
    intro z hz hne
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hne
    constructor
    · simp only [PiLp.smul_apply,smul_eq_mul,← Finset.mul_sum,hz,mul_zero]
    · simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  by_cases hs : S.Nonempty
  · obtain ⟨w,hw,hm⟩ := (actual_mean_zero_unit_sphere_compact n).exists_isMinOn hs
      (actual_laplacian_euclidean_quadratic_continuous G).continuousOn
    have hwne : w ≠ 0 := by intro h; simpa [h] using hw.2
    have hp := actual_connected_mean_zero_laplacian_positive G hg w hw.1 hwne
    refine ⟨LaplacianQuadratic G (fun i => w i),hp,?_⟩
    intro z hz
    by_cases hze : z = 0
    · simp [hze,LaplacianQuadratic]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hze
    have hb := hm (hu z hz hze)
    change LaplacianQuadratic G (fun i => w i) ≤ LaplacianQuadratic G (fun i => (‖z‖⁻¹ • z) i) at hb
    rw [actual_laplacian_euclidean_quadratic_smul] at hb
    have ht := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖z‖)
    have he : (‖z‖⁻¹)^2 * LaplacianQuadratic G (fun i => z i) * ‖z‖^2 =
        LaplacianQuadratic G (fun i => z i) := by field_simp [hn.ne']
    simpa only [he] using ht
  · refine ⟨1,by norm_num,?_⟩
    intro z hz
    have hze : z = 0 := by
      by_contra h
      exact hs ⟨_,hu z hz h⟩
    simp [hze,LaplacianQuadratic]

#print axioms actual_laplacian_euclidean_quadratic_continuous
#print axioms actual_laplacian_euclidean_quadratic_smul
#print axioms actual_mean_zero_unit_sphere_compact
#print axioms actual_connected_euclidean_poincare_exists
end Reference.MD06Correction
