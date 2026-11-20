module

public import NLA.MF05.PaperCyclicNorm

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.MF05.Paper.Cyclic

theorem corner_action (n : ℕ) (x : RealVector (n+1)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (corner n) x =
      EuclideanSpace.single (Fin.last n) (x 0) := by
  ext i
  change (Matrix.mulVec (Matrix.single (Fin.last n) 0 (1 : ℝ)) (fun j => x j)) i = _
  rw [Matrix.single_mulVec]
  simp [Function.update_apply]

theorem corner_norm (n : ℕ) : realSpectralNorm (corner n) = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    rw [corner_action]
    simpa using PiLp.norm_apply_le x 0
  · have h := (Matrix.toEuclideanCLM (𝕜 := ℝ) (corner n)).le_opNorm
      (EuclideanSpace.single (0 : Fin (n+1)) (1 : ℝ))
    rw [corner_action] at h
    simpa [realSpectralNorm] using h

theorem spectralNorm_sub_comm {d : ℕ} (A B : RealSquare d) :
    realSpectralNorm (A-B) = realSpectralNorm (B-A) := by
  rw [← neg_sub B A]
  simp only [realSpectralNorm, map_neg, norm_neg]

theorem singleton_hausdorff {d : ℕ} (A B : RealSquare d) :
    realHausdorff {A} {B} = realSpectralNorm (A-B) := by
  simp [realHausdorff, realDirectedDistance, realPointDistance, spectralNorm_sub_comm B A]

theorem perturbation_distance (n : ℕ) (δ : ℝ) :
    realHausdorff {shift n} {perturbation n δ} = |δ| := by
  rw [singleton_hausdorff, spectralNorm_sub_comm, perturbation_literal,
    add_sub_cancel_left]
  have hs : realSpectralNorm (δ • corner n) = |δ| * realSpectralNorm (corner n) := by
    simp [realSpectralNorm, map_smul, norm_smul, Real.norm_eq_abs]
  rw [hs, corner_norm, mul_one]

#print axioms perturbation_distance
end NLA.MF05.Paper.Cyclic
