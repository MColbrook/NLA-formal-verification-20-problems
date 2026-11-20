module

public import NLA.RA02.PaperInterpolationSelected
public import NLA.RA02.PaperInterpolationMissing
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem paper_interpolation_coefficients {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    interpolationCoefficients hs rows t = (prefixMatrix hs.le rows t)⁻¹ *ᵥ
      (fun i => lower n t (rows i) ⟨s,hs⟩) := by
  rfl

theorem paper_interpolation_residual {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    interpolationResidual hs rows t = (fun i => lower n t i ⟨s,hs⟩) -
      (lower n t).submatrix id (Fin.castLE hs.le) *ᵥ interpolationCoefficients hs rows t := by
  rfl

theorem paper_interpolation_euclidean_norm {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    interpolationSquaredNorm hs rows t =
      ‖(WithLp.toLp 2 (interpolationResidual hs rows t) : EuclideanSpace ℝ (Fin n))‖^2 := by
  exact (interpolation_actual_squared_norm hs rows t).symm

theorem paper_interpolation_selected_rows {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ i : Fin s, interpolationResidual hs rows t (rows i) = 0 := by
  filter_upwards [prefix_eventually_nonsingular hs.le rows] with t ht
  exact interpolation_vanishes_on_rows hs rows t
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ht))

theorem paper_interpolation_indicator_limit {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    Tendsto (fun t => (interpolationSquaredNorm hs rows t)⁻¹) (𝓝[>] 0)
      (𝓝 (if (⟨s,hs⟩ : Fin n) ∉ Set.range rows then 1 else 0)) := by
  by_cases hm : (⟨s,hs⟩ : Fin n) ∈ Set.range rows
  · rw [if_neg (not_not.mpr hm)]
    exact interpolation_selected_reciprocal_limit hs rows hm
  · rw [if_pos hm]
    exact interpolation_missing_reciprocal_limit hs rows hm

theorem paper_interpolation_lower_bound {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (1/4 : ℝ) ≤ interpolationSquaredNorm hs rows t := by
  exact interpolation_norm_lower_bound hs rows

end NLA.RA02.Paper

