module

public import NLA.RA02.PaperSpectralSplit
public import NLA.RA02.PaperPrefixInverse

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace NLA.RA02.Paper

def spectralCorrectionDiagonal (n s : ℕ) (t : ℝ) : Matrix (Fin s) (Fin s) ℝ :=
  Matrix.diagonal (fun i => t^(n^2*(s-i.val)-2*s))

def spectralCorrection {n s : ℕ} (hs : s ≤ n) (rows cols : Fin s ↪ Fin n) (t : ℝ) :
    Matrix (Fin s) (Fin s) ℝ :=
  spectralCorrectionDiagonal n s t * scaledPrefixInverse hs rows t *
    scaledSpectralTail rows cols t * (scaledPrefixInverse hs cols t).transpose

theorem spectral_exponent_gap {n s : ℕ} (hs : s < n) : 2*s < n^2 := by
  nlinarith [Nat.zero_le (s*s)]

theorem spectral_correction_exponent_pos {n s : ℕ} (hs : s < n) (i : Fin s) :
    0 < n^2*(s-i.val)-2*s := by
  have hi : 1 ≤ s-i.val := by omega
  have hg := spectral_exponent_gap hs
  have hm := Nat.mul_le_mul_left (n^2) hi
  simp only [mul_one] at hm
  omega

theorem continuous_spectralCorrectionDiagonal (n s : ℕ) :
    Continuous (spectralCorrectionDiagonal n s) := by
  apply continuous_matrix
  intro i j
  simp only [spectralCorrectionDiagonal, Matrix.diagonal_apply]
  split_ifs <;> fun_prop

theorem spectralCorrectionDiagonal_zero {n s : ℕ} (hs : s < n) :
    spectralCorrectionDiagonal n s 0 = 0 := by
  ext i j
  simp [spectralCorrectionDiagonal, Matrix.diagonal_apply,
    Nat.ne_of_gt (spectral_correction_exponent_pos hs i)]

theorem continuousAt_spectralCorrection {n s : ℕ} (hs : s ≤ n)
    (rows cols : Fin s ↪ Fin n) : ContinuousAt (spectralCorrection hs rows cols) 0 := by
  exact (((continuous_spectralCorrectionDiagonal n s).continuousAt.mul
    (continuousAt_scaledPrefixInverse hs rows)).mul
    (continuous_scaledSpectralTail rows cols).continuousAt).mul
    (continuous_id.matrix_transpose.continuousAt.comp
      (continuousAt_scaledPrefixInverse hs cols))

theorem spectralCorrection_zero {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n) :
    spectralCorrection hs.le rows cols 0 = 0 := by
  simp [spectralCorrection, spectralCorrectionDiagonal_zero hs]

theorem spectralCorrection_det_limit {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n) :
    Tendsto (fun t : ℝ => (1 + spectralCorrection hs.le rows cols t).det)
      (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun t : ℝ => (1 + spectralCorrection hs.le rows cols t).det) 0 :=
    continuous_id.matrix_det.continuousAt.comp
      (continuousAt_const.add (continuousAt_spectralCorrection hs.le rows cols))
  simpa only [spectralCorrection_zero hs, add_zero, Matrix.det_one] using
    hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from inf_le_left)

#print axioms spectralCorrection_det_limit
end NLA.RA02.Paper
