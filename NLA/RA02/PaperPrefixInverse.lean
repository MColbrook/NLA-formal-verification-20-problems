module

public import NLA.RA02.PaperPrefixFactorization
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical Topology
open Filter Asymptotics
namespace NLA.RA02.Paper

/-- Polynomial extension of t^s times the inverse prefix. -/
def scaledPrefixInverse {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Matrix (Fin s) (Fin s) ℝ :=
  Matrix.diagonal (fun j => if Fin.castLE hs j ∉ Set.range rows then
    t^(s-(j.val+1)) else t^s) * (normalizedPrefix hs rows t)⁻¹

theorem scaledPrefixInverse_eq {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n)
    {t : ℝ} (ht : t ≠ 0) :
    scaledPrefixInverse hs rows t = t^s • (prefixMatrix hs rows t)⁻¹ := by
  have hd : (Matrix.diagonal (fun j : Fin s =>
      if Fin.castLE hs j ∉ Set.range rows then t^(j.val+1) else 1))⁻¹ =
      Matrix.diagonal (fun j => (if Fin.castLE hs j ∉ Set.range rows then t^(j.val+1) else 1)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
      split_ifs <;> simp [ht]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [prefix_factorization, Matrix.mul_inv_rev, hd, ← Matrix.smul_mul]
  unfold scaledPrefixInverse
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    change (if Fin.castLE hs i ∉ Set.range rows then t^(s-(i.val+1)) else t^s) =
      t^s * (if Fin.castLE hs i ∉ Set.range rows then t^(i.val+1) else 1)⁻¹
    by_cases hm : Fin.castLE hs i ∉ Set.range rows
    · simp only [if_pos hm]
      exact pow_sub₀ t ht (by omega)
    · simp only [if_neg hm, inv_one, mul_one]
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, hij]

theorem continuousAt_scaledPrefixInverse {n s : ℕ} (hs : s ≤ n)
    (rows : Fin s ↪ Fin n) : ContinuousAt (scaledPrefixInverse hs rows) 0 := by
  have hi : ContinuousAt (fun t : ℝ => (normalizedPrefix hs rows t)⁻¹) 0 := by
    apply (continuousAt_matrix_inv _ _).comp (continuous_normalizedPrefix hs rows).continuousAt
    simpa only [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv] using
      (continuousAt_inv₀ (normalizedPrefix_zero_det_ne_zero hs rows))
  unfold scaledPrefixInverse
  apply ContinuousAt.mul _ hi
  apply Continuous.continuousAt
  apply continuous_matrix
  intro i j
  simp only [Matrix.diagonal_apply]
  split_ifs <;> fun_prop

theorem continuous_real_euclidean_operator {s : ℕ} :
    Continuous (fun A : Matrix (Fin s) (Fin s) ℝ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) A) := by
  let f := (Matrix.toEuclideanCLM (n := Fin s) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact f.continuous_of_finiteDimensional

theorem prefix_inverse_bound {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (prefixMatrix hs rows t)⁻¹‖ ≤ C / t^s := by
  let B := fun t : ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ) (scaledPrefixInverse hs rows t)
  have hc : ContinuousAt B 0 := continuous_real_euclidean_operator.continuousAt.comp
    (continuousAt_scaledPrefixInverse hs rows)
  refine ⟨‖B 0‖+1, by positivity, ?_⟩
  have he := hc.norm.eventually (gt_mem_nhds (show ‖B 0‖ < ‖B 0‖+1 by linarith))
  filter_upwards [he.filter_mono inf_le_left, self_mem_nhdsWithin] with t hb ht
  have hp : 0 < t^s := pow_pos ht _
  apply (le_div_iff₀ hp).mpr
  have hB : ‖B t‖ = t^s * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (prefixMatrix hs rows t)⁻¹‖ := by
    dsimp [B]
    rw [scaledPrefixInverse_eq hs rows (ne_of_gt ht), map_smul, norm_smul,
      Real.norm_eq_abs, abs_of_pos hp]
  rw [mul_comm, ← hB]
  exact hb.le

#print axioms prefix_inverse_bound
end NLA.RA02.Paper
