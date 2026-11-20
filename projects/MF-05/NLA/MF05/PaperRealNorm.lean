module

public import NLA.MF05.PaperRealDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
namespace NLA.MF05.Paper

def embedVector {d : ℕ} (x : RealVector d) : NLA.MF07.EuclideanVector d :=
  WithLp.toLp 2 (fun i => (x i : ℂ))
def realVector {d : ℕ} (z : NLA.MF07.EuclideanVector d) : RealVector d :=
  WithLp.toLp 2 (fun i => (z i).re)
def imagVector {d : ℕ} (z : NLA.MF07.EuclideanVector d) : RealVector d :=
  WithLp.toLp 2 (fun i => (z i).im)

theorem embedVector_norm {d : ℕ} (x : RealVector d) : ‖embedVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [EuclideanSpace.norm_sq_eq, embedVector]

theorem complex_norm_split {d : ℕ} (z : NLA.MF07.EuclideanVector d) :
    ‖z‖^2 = ‖realVector z‖^2 + ‖imagVector z‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change ‖z i‖^2 = (z i).re^2 + (z i).im^2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem complex_action_embed {d : ℕ} (A : RealSquare d) (x : RealVector d) :
    Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify A) (embedVector x) =
      embedVector (Matrix.toEuclideanCLM (𝕜:=ℝ) A x) := by
  ext i
  change (∑ j, (A i j : ℂ) * (x j : ℂ)) = ((∑ j, A i j * x j : ℝ) : ℂ)
  simp

theorem complex_action_real {d : ℕ} (A : RealSquare d) (z : NLA.MF07.EuclideanVector d) :
    realVector (Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify A) z) =
      Matrix.toEuclideanCLM (𝕜:=ℝ) A (realVector z) := by
  ext i
  change (∑ j, (A i j : ℂ) * z j).re = ∑ j, A i j * (z j).re
  simp

theorem complex_action_imag {d : ℕ} (A : RealSquare d) (z : NLA.MF07.EuclideanVector d) :
    imagVector (Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify A) z) =
      Matrix.toEuclideanCLM (𝕜:=ℝ) A (imagVector z) := by
  ext i
  change (∑ j, (A i j : ℂ) * z j).im = ∑ j, A i j * (z j).im
  simp

theorem complexify_spectralNorm {d : ℕ} (A : RealSquare d) :
    NLA.MF07.spectralNorm (complexify A) = realSpectralNorm A := by
  let T := Matrix.toEuclideanCLM (𝕜:=ℝ) A
  let S := Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify A)
  change ‖S‖ = ‖T‖
  apply le_antisymm
  · apply S.opNorm_le_bound (norm_nonneg _)
    intro z
    have hr := (sq_le_sq₀ (norm_nonneg (T (realVector z)))
      (mul_nonneg (norm_nonneg T) (norm_nonneg (realVector z)))).mpr (T.le_opNorm (realVector z))
    have hi := (sq_le_sq₀ (norm_nonneg (T (imagVector z)))
      (mul_nonneg (norm_nonneg T) (norm_nonneg (imagVector z)))).mpr (T.le_opNorm (imagVector z))
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    have hz := complex_norm_split z
    have hs := complex_norm_split (S z)
    change ‖S z‖^2 = ‖realVector (Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify A) z)‖^2 +
      ‖imagVector (Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify A) z)‖^2 at hs
    rw [complex_action_real, complex_action_imag] at hs
    change ‖S z‖^2 = ‖T (realVector z)‖^2 + ‖T (imagVector z)‖^2 at hs
    simpa only [hs, mul_pow, hz, mul_add] using add_le_add hr hi
  · apply T.opNorm_le_bound (norm_nonneg _)
    intro x
    have h := S.le_opNorm (embedVector x)
    change ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify A) (embedVector x)‖ ≤
      ‖S‖ * ‖embedVector x‖ at h
    rw [complex_action_embed, embedVector_norm, embedVector_norm] at h
    exact h

#print axioms complexify_spectralNorm
end NLA.MF05.Paper
