module

public import NLA.RA02.PaperSpectralCorrection

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace NLA.RA02.Paper

theorem spectral_diagonal_product {n s : ℕ} (hs : s < n) (t : ℝ) :
    Matrix.diagonal (fun i : Fin s => epsilon n t^i.val) *
      spectralCorrectionDiagonal n s t = t^(n^2*s-2*s) • (1 : Matrix (Fin s) (Fin s) ℝ) := by
  rw [spectralCorrectionDiagonal, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    have hi : i.val ≤ s := i.isLt.le
    have hg := spectral_correction_exponent_pos hs i
    have he : n^2*(s-i.val)+n^2*i.val = n^2*s := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hi]
    have he' : n^2*i.val+(n^2*(s-i.val)-2*s) = n^2*s-2*s := by omega
    rw [epsilon, ← pow_mul, ← pow_add, he']
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.one_apply_ne hij]

theorem prefix_scaled_inverse_cancel {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n)
    {t : ℝ} (ht : t ≠ 0) (hu : IsUnit (prefixMatrix hs rows t)) :
    prefixMatrix hs rows t * scaledPrefixInverse hs rows t = t^s • 1 := by
  rw [scaledPrefixInverse_eq hs rows ht, Matrix.mul_smul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu)]

theorem spectral_factorization {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n)
    {t : ℝ} (ht : t ≠ 0) (hu : IsUnit (prefixMatrix hs.le rows t))
    (hv : IsUnit (prefixMatrix hs.le cols t)) :
    (sharpFamily n t).submatrix rows cols =
      prefixMatrix hs.le rows t * Matrix.diagonal (fun i : Fin s => epsilon n t^i.val) *
        (1 + spectralCorrection hs.le rows cols t) * (prefixMatrix hs.le cols t).transpose := by
  rw [spectral_split hs.le rows cols t, mul_add, mul_one, add_mul]
  congr 1
  unfold spectralCorrection
  let U := prefixMatrix hs.le rows t
  let V := prefixMatrix hs.le cols t
  let D := Matrix.diagonal (fun i : Fin s => epsilon n t^i.val)
  let B := scaledPrefixInverse hs.le rows t
  let C := scaledPrefixInverse hs.le cols t
  let T := scaledSpectralTail rows cols t
  change epsilon n t^s • T = U * D * (spectralCorrectionDiagonal n s t * B * T * C.transpose) * V.transpose
  have hd := spectral_diagonal_product hs t
  change D * spectralCorrectionDiagonal n s t = _ at hd
  calc
    _ = t^(n^2*s-2*s) • ((U*B) * T * (V*C).transpose) := by
      rw [prefix_scaled_inverse_cancel hs.le rows ht hu, prefix_scaled_inverse_cancel hs.le cols ht hv]
      simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
        Matrix.mul_smul, one_mul, mul_one, smul_smul]
      congr 1
      have he : 2*s ≤ n^2*s := by
        by_cases hz : s = 0
        · simp [hz]
        · have hn : 2 ≤ n^2 := by have := spectral_exponent_gap hs; omega
          nlinarith
      rw [epsilon, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega
    _ = _ := by
      rw [Matrix.transpose_mul]
      calc
        _ = U * (t^(n^2*s-2*s) • 1) * B * T * C.transpose * V.transpose := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [← hd]; noncomm_ring

#print axioms spectral_factorization
end NLA.RA02.Paper
