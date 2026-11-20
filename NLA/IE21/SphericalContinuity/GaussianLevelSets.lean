module

public import NLA.IE21.Definitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace NLA.IE21.SphericalContinuity
local instance : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)

theorem quadratic_level_finite {a b : ℝ} (ha : a ≠ 0) :
    {t : ℝ | a * t ^ 2 + b = 0}.Finite := by
  have hf : ({Real.sqrt (-b / a), -Real.sqrt (-b / a)} : Set ℝ).Finite :=
    by simp
  apply hf.subset
  intro t ht
  change a * t ^ 2 + b = 0 at ht
  have he : t ^ 2 = -b / a := (eq_div_iff ha).mpr (by nlinarith [ht])
  have hn : 0 ≤ -b / a := he ▸ sq_nonneg t
  have hs : t ^ 2 = (Real.sqrt (-b / a)) ^ 2 := he.trans (Real.sq_sqrt hn).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h <;> simp [h]

/-- A diagonal nonzero quadratic polynomial vanishes on a null set under the
actual product of independent standard real Gaussians. -/
theorem gaussian_diagonal_quadratic_zero (n : ℕ) (c : Fin n → ℝ)
    (hc : ∃ i, c i ≠ 0) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) {g | ∑ i, c i * (g i) ^ 2 = 0} = 0 := by
  cases n with
  | zero => obtain ⟨i, _⟩ := hc; exact Fin.elim0 i
  | succ n =>
    obtain ⟨i, hi⟩ := hc
    let π : Measure (Fin n → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
    have he : MeasurePreserving e ((gaussianReal 0 1).prod π)
        (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => gaussianReal 0 1) i).symm
    let S : Set (Fin (n+1) → ℝ) := {g | ∑ j, c j * (g j) ^ 2 = 0}
    have hm : MeasurableSet S := measurableSet_eq_fun (by fun_prop) measurable_const
    change (Measure.pi (fun _ : Fin (n+1) => gaussianReal 0 1)) S = 0
    rw [← he.map_eq, Measure.map_apply e.measurable hm, Measure.prod_apply_symm (hm.preimage e.measurable)]
    have hz (g : Fin n → ℝ) :
        (gaussianReal 0 1) ((fun t : ℝ => (t,g)) ⁻¹' (e ⁻¹' S)) = 0 := by
      have hform (t : ℝ) : (∑ j, c j * (e (t,g) j) ^ 2) =
          c i * t ^ 2 + ∑ j : Fin n, c (i.succAbove j) * (g j) ^ 2 := by
        rw [i.sum_univ_succAbove]
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
      have hs : (fun t : ℝ => (t,g)) ⁻¹' (e ⁻¹' S) =
          {t | c i * t ^ 2 + ∑ j : Fin n, c (i.succAbove j) * (g j) ^ 2 = 0} := by
        ext t
        change (∑ j, c j * (e (t,g) j) ^ 2) = 0 ↔ _
        rw [hform]
        rfl
      rw [hs]
      exact (quadratic_level_finite hi).measure_zero _
    simp_rw [hz]
    simp

#print axioms gaussian_diagonal_quadratic_zero
end NLA.IE21.SphericalContinuity
