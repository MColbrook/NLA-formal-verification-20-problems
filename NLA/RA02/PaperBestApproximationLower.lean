module

/- Frobenius norm/trace identities adapted from the credited RA-03 Proof and
RA-09 ComplexFrobenius modules. Copyright (c) 2026 George Stepaniants;
Apache 2.0. Additional paper-specific formalization with Codex assistance. -/
public import NLA.RA02.PaperSingularTail
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix Matrix.Norms.Frobenius
namespace NLA.RA02.Paper

theorem actual_frobenius_norm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    NLA.RA03.frobeniusSq A = ‖A‖^2 := by
  simp only [Matrix.frobenius_norm_def, Real.rpow_two, ← Real.sqrt_eq_rpow]
  rw [Real.sq_sqrt (by positivity)]
  simp only [NLA.RA03.frobeniusSq, Complex.normSq_eq_norm_sq]

theorem frobenius_mulVec_bound {n : ℕ} (A : NLA.RA02.Square n) (v : Fin n → ℂ) :
    ‖(WithLp.toLp 2 (A *ᵥ v) : EuclideanSpace ℂ (Fin n))‖ ≤
      ‖A‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin n))‖ := by
  have he : A * Matrix.replicateCol (Fin 1) v = Matrix.replicateCol (Fin 1) (A *ᵥ v) := by
    ext i j
    rfl
  have hh := Matrix.frobenius_norm_mul A (Matrix.replicateCol (Fin 1) v)
  rw [he, Matrix.frobenius_norm_replicateCol, Matrix.frobenius_norm_replicateCol] at hh
  exact hh

theorem low_rank_has_kernel (r : ℕ) (B : NLA.RA02.Square (r+1)) (hB : B.rank ≤ r) :
    ∃ v : Fin (r+1) → ℂ, v ≠ 0 ∧ B *ᵥ v = 0 := by
  have hnu : ¬IsUnit B := by
    intro hu
    have hr := Matrix.rank_of_isUnit B hu
    simp only [Fintype.card_fin] at hr
    omega
  have hni : ¬Function.Injective B.mulVec := fun hi => hnu (Matrix.mulVec_injective_iff_isUnit.mp hi)
  obtain ⟨x,y,hxy,hne⟩ := Function.not_injective_iff.mp hni
  refine ⟨x-y, sub_ne_zero.mpr hne, ?_⟩
  rw [Matrix.mulVec_sub, hxy, sub_self]

theorem best_error_lower (r : ℕ) (A B : NLA.RA02.Square (r+1))
    (hA : A.PosDef) (hB : B.rank ≤ r) :
    NLA.RA03.singularTailSq A r ≤ NLA.RA03.frobeniusSq (A-B) := by
  obtain ⟨v,hv,hBv⟩ := low_rank_has_kernel r B hB
  let x : EuclideanSpace ℂ (Fin (r+1)) := WithLp.toLp 2 v
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr (by simpa [x] using hv)
  have hvA : A⁻¹ *ᵥ ((A-B) *ᵥ v) = v := by
    rw [Matrix.sub_mulVec, hBv, sub_zero, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit), Matrix.one_mulVec]
  have hop := (Matrix.toEuclideanCLM (𝕜:=ℂ) A⁻¹).le_opNorm
    (WithLp.toLp 2 ((A-B) *ᵥ v))
  rw [Matrix.toEuclideanCLM_toLp, hvA] at hop
  have hf := frobenius_mulVec_bound (A-B) v
  have hnorm : ‖x‖ ≤ ‖Matrix.toEuclideanCLM (𝕜:=ℂ) A⁻¹‖ * (‖A-B‖ * ‖x‖) :=
    hop.trans (mul_le_mul_of_nonneg_left hf (norm_nonneg _))
  rw [← mul_assoc] at hnorm
  have hprod : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜:=ℂ) A⁻¹‖ * ‖A-B‖ :=
    (mul_le_mul_iff_left₀ hx).mp (by simpa only [one_mul, mul_comm ‖x‖] using hnorm)
  rw [inverse_norm_last_eigenvalue r A hA] at hprod
  have hpos := NLA.RA02.orderedEigenvalues_pos A hA hA.isHermitian (Fin.last r)
  have hl : NLA.RA02.orderedEigenvalues A hA.isHermitian (Fin.last r) ≤ ‖A-B‖ := by
    have hm := mul_le_mul_of_nonneg_left hprod hpos.le
    field_simp at hm
    exact hm
  rw [singularTailSq_last, singular_last_sq_eq_eigenvalue_sq r A hA, actual_frobenius_norm_sq]
  exact pow_le_pow_left₀ hpos.le hl 2

#print axioms best_error_lower
end NLA.RA02.Paper
