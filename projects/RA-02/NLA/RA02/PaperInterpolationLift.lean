module

public import NLA.RA02.PaperInterpolationEquations
public import NLA.RA02.PaperSpectralSplit

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
namespace NLA.RA02.Paper

def embedPrefixCoefficients {n s : ℕ} (hs : s < n) (c : Fin s → ℝ) : Fin n → ℝ :=
  fun i => if hi : i.val < s then c ⟨i.val,hi⟩ else 0

def liftedInterpolationVector {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Fin n → ℝ := Pi.single ⟨s,hs⟩ 1 - embedPrefixCoefficients hs (interpolationCoefficients hs rows t)

theorem lifted_next_entry {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    liftedInterpolationVector hs rows t ⟨s,hs⟩ = 1 := by
  simp [liftedInterpolationVector, embedPrefixCoefficients]

theorem lower_mulVec_embed {n s : ℕ} (hs : s < n) (t : ℝ) (c : Fin s → ℝ) :
    lower n t *ᵥ embedPrefixCoefficients hs c =
      (lower n t).submatrix id (Fin.castLE hs.le) *ᵥ c := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, id_eq]
  calc
    _ = ∑ j : Fin n, if j.val < s then lower n t i j * embedPrefixCoefficients hs c j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.val < s <;> simp [embedPrefixCoefficients, hj]
    _ = ∑ j : Fin s, lower n t i (Fin.castLE hs.le j) *
        embedPrefixCoefficients hs c (Fin.castLE hs.le j) :=
      sum_initial_segment hs.le _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      simp [embedPrefixCoefficients, j.isLt]

theorem interpolation_as_lower_mulVec {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    lower n t *ᵥ liftedInterpolationVector hs rows t = interpolationResidual hs rows t := by
  rw [liftedInterpolationVector, Matrix.mulVec_sub, lower_mulVec_embed]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, nextColumn]

theorem interpolation_actual_squared_norm {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    ‖(WithLp.toLp 2 (interpolationResidual hs rows t) : EuclideanSpace ℝ (Fin n))‖^2 =
      interpolationSquaredNorm hs rows t := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i, ‖interpolationResidual hs rows t i‖^2) = ∑ i, (interpolationResidual hs rows t i)^2
  simp only [Real.norm_eq_abs, sq_abs]

#print axioms interpolation_as_lower_mulVec
end NLA.RA02.Paper
