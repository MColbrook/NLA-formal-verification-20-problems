module

public import NLA.IE21.GaussianPolar
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology RealInnerProductSpace
namespace NLA.IE21.SphericalContinuity

theorem gaussianDirection_isometry {n : ℕ} (e : Space n ≃ₗᵢ[ℝ] Space n) (g : Space n) :
    e (gaussianDirection g) = gaussianDirection (e g) := by
  simp [gaussianDirection, map_smul]

/-- Orthogonal invariance of the actual normalized surface measure, derived
from its proved Gaussian normalization map. -/
theorem sphereLaw_isometry (n : ℕ) (hn : 1 ≤ n) (e : Space n ≃ₗᵢ[ℝ] Space n) :
    (sphereLaw n).map e = sphereLaw n := by
  calc
    (sphereLaw n).map e = ((stdGaussian (Space n)).map gaussianDirection).map e := by
      rw [gaussian_direction_law n hn]
    _ = (stdGaussian (Space n)).map (fun g => e (gaussianDirection g)) := by
      rw [Measure.map_map e.continuous.measurable (measurable_gaussianDirection n)]
      rfl
    _ = (stdGaussian (Space n)).map (fun g => gaussianDirection (e g)) := by
      congr 1
      funext g
      exact gaussianDirection_isometry e g
    _ = ((stdGaussian (Space n)).map e).map gaussianDirection := by
      rw [Measure.map_map (measurable_gaussianDirection n) e.continuous.measurable]
      rfl
    _ = sphereLaw n := by rw [stdGaussian_map e, gaussian_direction_law n hn]

/-- Every unit direction has the same squared-projection law under the
literal sphere measure used by the paper. -/
theorem directionalEnergy_law_eq (n : ℕ) (hn : 1 ≤ n) (x y : Space n)
    (hxy : ‖x‖ = ‖y‖) :
    (sphereLaw n).map (directionalEnergy x) = (sphereLaw n).map (directionalEnergy y) := by
  let e : Space n ≃ₗᵢ[ℝ] Space n := (ℝ ∙ (x - y))ᗮ.reflection
  have he : e x = y := Submodule.reflection_sub hxy
  have hf : (fun u => directionalEnergy y (e u)) = directionalEnergy x := by
    funext u
    rw [← he]
    simp [directionalEnergy]
  calc
    (sphereLaw n).map (directionalEnergy x) = ((sphereLaw n).map e).map (directionalEnergy y) := by
      rw [Measure.map_map (by unfold directionalEnergy; fun_prop) e.continuous.measurable]
      exact congrArg (Measure.map · (sphereLaw n)) hf.symm
    _ = (sphereLaw n).map (directionalEnergy y) := by rw [sphereLaw_isometry n hn e]

#print axioms sphereLaw_isometry
#print axioms directionalEnergy_law_eq
end NLA.IE21.SphericalContinuity
