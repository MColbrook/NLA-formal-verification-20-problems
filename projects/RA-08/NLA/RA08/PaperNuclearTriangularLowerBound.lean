module

public import NLA.RA08.PaperNuclearTriangularSpectrum
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearTriangular_singular_lower {m : ℕ} (hm : 1 ≤ m) (j : Fin m) :
    1/(Real.pi*((j.val+1 : ℕ) : ℝ)) ≤
      (1/(2*Real.sin (nuclearSineAngle j/2)))/(m : ℝ) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hθ := nuclearSineAngle_pos j
  have hs : 0 < Real.sin (nuclearSineAngle j/2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [nuclearSineAngle_lt_pi j,Real.pi_pos])
  have ha : ((j.val+1 : ℕ) : ℝ)*Real.pi-2*m*(nuclearSineAngle j/2) =
      ((m : ℝ)+j.val+1)*Real.pi/(2*m+1) := by
    unfold nuclearSineAngle
    push_cast
    field_simp
    ring
  have hbound : m*(2*Real.sin (nuclearSineAngle j/2)) ≤
      Real.pi*((j.val+1 : ℕ) : ℝ) := by
    have hsin := Real.sin_le (by linarith : 0 ≤ nuclearSineAngle j/2)
    have hmul := mul_le_mul_of_nonneg_left hsin (by positivity : (0 : ℝ) ≤ 2*m)
    have hnonneg : 0 ≤ ((m : ℝ)+j.val+1)*Real.pi/(2*m+1) := by positivity
    nlinarith
  rw [div_div,show 2*Real.sin (nuclearSineAngle j/2)*(m : ℝ)=
    m*(2*Real.sin (nuclearSineAngle j/2)) by ring]
  exact one_div_le_one_div_of_le (by positivity) hbound

theorem nuclearTriangular_nuclearNorm_lower (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m+1)/Real.pi ≤ nuclearNorm (nuclearTriangular m)/(m : ℝ) := by
  have hh : (harmonic m : ℝ)=∑ j : Fin m, (((j.val+1 : ℕ) : ℝ))⁻¹ := by
    simp only [harmonic,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact (Fin.sum_univ_eq_sum_range _ m).symm
  calc
    Real.log (m+1)/Real.pi ≤ (harmonic m : ℝ)/Real.pi := by
      apply div_le_div_of_nonneg_right _ Real.pi_pos.le
      simpa only [Nat.cast_add,Nat.cast_one] using log_add_one_le_harmonic m
    _ = ∑ j : Fin m, 1/(Real.pi*((j.val+1 : ℕ) : ℝ)) := by
      rw [hh,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      rw [← one_div,div_div,mul_comm]
    _ ≤ ∑ j : Fin m, (1/(2*Real.sin (nuclearSineAngle j/2)))/(m : ℝ) :=
      Finset.sum_le_sum fun j _ => nuclearTriangular_singular_lower hm j
    _ = nuclearNorm (nuclearTriangular m)/(m : ℝ) := by
      rw [nuclearTriangular_nuclearNorm,Finset.sum_div]

#print axioms nuclearTriangular_nuclearNorm_lower
end NLA.RA08.Paper
