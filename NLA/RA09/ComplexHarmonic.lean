module

/- Complex adaptation of the diagonal quadratic test in Harmonic.lean.
Copyright (c) 2026 George Stepaniants. Apache 2.0; see LICENSE.
Complex-field adaptation with Codex assistance. -/
public import NLA.RA09.ComplexDefinitions
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder ComplexOrder
open Matrix
namespace NLA.RA09.ComplexPaper

def outerSquare {n : ℕ} (v : Fin n → ℂ) : ComplexMatrix n := vecMulVec v (star v)

theorem outerSquare_mulVec {n : ℕ} (v z : Fin n → ℂ) :
    outerSquare v *ᵥ z = (star v ⬝ᵥ z) • v := by
  ext i
  simp only [mulVec, dotProduct, outerSquare, vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem diagonal_outer_quadratic {n : ℕ} (a : Fin n → ℝ) (v z : Fin n → ℂ) (b : ℝ) :
    star z ⬝ᵥ ((diagonal (fun i => (a i : ℂ)) - (b : ℂ) • outerSquare v) *ᵥ z) =
      ((∑ i, a i * Complex.normSq (z i) : ℝ) : ℂ) -
        (b : ℂ) * (Complex.normSq (star v ⬝ᵥ z) : ℂ) := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
    outerSquare_mulVec, dotProduct_smul]
  have hstar : star (star v ⬝ᵥ z) = star z ⬝ᵥ v := by
    simp [dotProduct, star_mul, mul_comm]
  simp only [smul_eq_mul, mulVec_diagonal, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.normSq_eq_conj_mul_self, ← Complex.star_def]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.star_apply]
    ring
  · change _ = (b : ℂ) * (star (star v ⬝ᵥ z) * (star v ⬝ᵥ z))
    rw [hstar]
    simp only [dotProduct]
    ring

theorem harmonic_constraint_proved {n : ℕ} (a : Fin n → ℝ) (v : Fin n → ℂ) (b : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : 0 < b)
    (horder : (diagonal (fun i => (a i : ℂ)) - (b : ℂ) • outerSquare v).PosSemidef) :
    (∀ i, a i = 0 → v i = 0) ∧ b * (∑ i, Complex.normSq (v i) / a i) ≤ 1 := by
  have hsupport : ∀ i, a i = 0 → v i = 0 := by
    intro i hi
    have hd := horder.diag_nonneg (i := i)
    have he : (diagonal (fun i => (a i : ℂ)) - (b : ℂ) • outerSquare v) i i =
        ((a i - b * Complex.normSq (v i) : ℝ) : ℂ) := by
      simp [outerSquare, vecMulVec_apply, Pi.star_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
        Complex.star_def, Complex.mul_conj, mul_assoc]
    rw [he] at hd
    have hd' : 0 ≤ a i - b * Complex.normSq (v i) := by exact_mod_cast hd
    have hz : Complex.normSq (v i) = 0 := by
      nlinarith [Complex.normSq_nonneg (v i)]
    exact Complex.normSq_eq_zero.mp hz
  refine ⟨hsupport, ?_⟩
  let H : ℝ := ∑ i, Complex.normSq (v i) / a i
  have hH : 0 ≤ H := Finset.sum_nonneg fun i _ =>
    div_nonneg (Complex.normSq_nonneg _) (ha i)
  by_cases hz : H = 0
  · change b * H ≤ 1
    simp [hz]
  have hHpos : 0 < H := lt_of_le_of_ne hH (Ne.symm hz)
  let z : Fin n → ℂ := fun i => v i / (a i : ℂ)
  have hdiag : (∑ i, a i * Complex.normSq (z i)) = H := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : a i = 0
    · simp [z, hi]
    · dsimp [z]
      rw [map_div₀, Complex.normSq_ofReal]
      field_simp
  have hdot : star v ⬝ᵥ z = (H : ℂ) := by
    simp only [dotProduct, H, Complex.ofReal_sum, Complex.ofReal_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [z, Pi.star_apply, Complex.normSq_eq_conj_mul_self, ← Complex.star_def]
    ring
  have hq := horder.re_dotProduct_nonneg z
  rw [diagonal_outer_quadratic, hdiag, hdot] at hq
  have hq' : 0 ≤ H - b * H^2 := by simpa [Complex.normSq_ofReal, pow_two] using hq
  change b * H ≤ 1
  apply (mul_le_mul_iff_right₀ hHpos).mp
  nlinarith [hq']

#print axioms harmonic_constraint_proved
end NLA.RA09.ComplexPaper
