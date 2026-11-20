module

public import NLA.IE21.SphericalContinuity.Rotation
public import NLA.IE21.SphericalContinuity.GaussianLevelSets

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators RealInnerProductSpace
namespace NLA.IE21.SphericalContinuity

theorem normalized_coordinate_level_polynomial {n : ℕ} (i : Fin n) (a : ℝ)
    (g : Space n)
    (h : directionalEnergy (EuclideanSpace.basisFun (Fin n) ℝ i)
      (gaussianDirection g) = a) :
    (n : ℝ) * (g i) ^ 2 - a * ∑ j, (g j) ^ 2 = 0 := by
  have hs := EuclideanSpace.real_norm_sq_eq g
  by_cases hz : g = 0
  · subst g
    simp
  · have hn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hh : (n : ℝ) * (‖g‖⁻¹ * g i) ^ 2 = a := by
      simpa only [directionalEnergy, EuclideanSpace.inner_basisFun_real,
        gaussianDirection, PiLp.smul_apply, smul_eq_mul] using h
    have he : (n : ℝ) * (g i) ^ 2 = a * ‖g‖ ^ 2 := by
      field_simp at hh
      nlinarith [hh]
    rw [← hs]
    linarith

theorem coordinate_energy_gaussian_level_zero (n : ℕ) (hn : 2 ≤ n)
    (i : Fin n) (a : ℝ) :
    (stdGaussian (Space n))
      {g | directionalEnergy (EuclideanSpace.basisFun (Fin n) ℝ i)
        (gaussianDirection g) = a} = 0 := by
  classical
  let c : Fin n → ℝ := fun j => if j = i then (n : ℝ) - a else -a
  have hc : ∃ j, c j ≠ 0 := by
    by_cases ha : (n : ℝ) - a = 0
    · haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
      obtain ⟨j, hji⟩ := exists_ne i
      refine ⟨j, ?_⟩
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      simp only [c, if_neg hji]
      linarith
    · exact ⟨i, by simpa [c] using ha⟩
  have hf (g : Fin n → ℝ) :
      (∑ j, c j * (g j) ^ 2) = (n : ℝ) * (g i) ^ 2 - a * ∑ j, (g j) ^ 2 := by
    calc
      _ = ∑ j, ((if j = i then (n : ℝ) * (g j) ^ 2 else 0) - a * (g j) ^ 2) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i <;> simp [c, hji] <;> ring
      _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]; simp
  have hz := gaussian_diagonal_quadratic_zero n c hc
  have hm : Measurable (fun g : Space n =>
      directionalEnergy (EuclideanSpace.basisFun (Fin n) ℝ i) (gaussianDirection g)) :=
    (by unfold directionalEnergy; fun_prop : Measurable
      (directionalEnergy (EuclideanSpace.basisFun (Fin n) ℝ i))).comp
        (measurable_gaussianDirection n)
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_apply (by fun_prop) (measurableSet_eq_fun hm measurable_const)]
  apply measure_mono_null (t := {g | ∑ j, c j * (g j) ^ 2 = 0}) _ hz
  intro g hg
  change directionalEnergy (EuclideanSpace.basisFun (Fin n) ℝ i)
    (gaussianDirection (WithLp.toLp 2 g)) = a at hg
  change (∑ j, c j * (g j) ^ 2) = 0
  rw [hf]
  exact normalized_coordinate_level_polynomial i a (WithLp.toLp 2 g) hg

/-- The squared projection in any unit direction has no atoms under the
actual normalized Euclidean surface measure, in every dimension at least two. -/
theorem directionalEnergy_atomless (n : ℕ) (hn : 2 ≤ n) (x : Space n)
    (hx : ‖x‖ = 1) : NullSingletonClass ((sphereLaw n).map (directionalEnergy x)) := by
  have hn1 : 1 ≤ n := by omega
  let i : Fin n := ⟨0, by omega⟩
  let b : Space n := EuclideanSpace.basisFun (Fin n) ℝ i
  have hb : ‖b‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one i
  have he := directionalEnergy_law_eq n hn1 x b (hx.trans hb.symm)
  rw [he]
  constructor
  intro a
  rw [Measure.map_apply (by unfold directionalEnergy; fun_prop) (measurableSet_singleton a)]
  rw [← gaussian_direction_law n hn1]
  rw [Measure.map_apply (measurable_gaussianDirection n)
    ((measurableSet_singleton a).preimage (by unfold directionalEnergy; fun_prop))]
  exact coordinate_energy_gaussian_level_zero n hn i a

#print axioms directionalEnergy_atomless
end NLA.IE21.SphericalContinuity
