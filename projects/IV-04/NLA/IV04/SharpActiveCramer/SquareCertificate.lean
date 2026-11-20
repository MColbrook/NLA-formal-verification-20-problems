module

/- Actual square integer Cramer numerator/common denominator bounds n! H^n. -/
public import NLA.IV04.SharpActiveCramer.RowSelection

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04SharpActiveCramer
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment

def sharpCertificateBound (n H : ℕ) : ℕ := n.factorial*H^n

theorem integer_square_system_sharp_certificate {n : ℕ}
    (N : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (x : Fin n → ℝ) (H : ℕ)
    (hN : ∀ i j, |N i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ))
    (hdet : N.det ≠ 0) (hx : integerRealMatrix N *ᵥ x=integerRealVector b) :
    ∃ p : Fin n → ℤ, ∃ d : ℤ, d ≠ 0 ∧ |d| ≤ (sharpCertificateBound n H : ℤ) ∧
      (∀ j, |p j| ≤ (sharpCertificateBound n H : ℤ)) ∧
      ∀ j, x j=(p j : ℝ)/(d : ℝ) := by
  have hcast : (N.det : ℝ)=(integerRealMatrix N).det := (Int.castRingHom ℝ).map_det N
  have hdetR : (integerRealMatrix N).det ≠ 0 := by
    rw [← hcast]
    exact_mod_cast hdet
  have hu : IsUnit (integerRealMatrix N) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdetR)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
  let y := (integerRealMatrix N).det⁻¹ • (integerRealMatrix N).cramer (integerRealVector b)
  have hy : integerRealMatrix N *ᵥ y=integerRealVector b := by
    dsimp [y]
    rw [Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ hdetR,one_smul]
  have hxy : x=y := hinj (hx.trans hy.symm)
  have hdQ : |N.det| ≤ (sharpCertificateBound n H : ℤ) := by
    simpa [sharpCertificateBound] using integer_det_entry_bound N H hN
  have hpQ (j : Fin n) : |(N.updateCol j b).det| ≤ (sharpCertificateBound n H : ℤ) := by
    apply (integer_det_entry_bound (N.updateCol j b) H ?_).trans_eq
      (by simp [sharpCertificateBound])
    intro i k
    by_cases hk : k=j
    · subst k
      simpa using hb i
    · simpa [Matrix.updateCol,hk] using hN i k
  refine ⟨fun j => (N.updateCol j b).det,N.det,hdet,hdQ,hpQ,?_⟩
  intro j
  have hnum : (((N.updateCol j b).det : ℤ) : ℝ)=
      ((integerRealMatrix N).updateCol j (integerRealVector b)).det := by
    calc
      _ = (integerRealMatrix (N.updateCol j b)).det := (Int.castRingHom ℝ).map_det _
      _ = _ := by
        congr 1
        exact Matrix.map_updateCol (Int.castRingHom ℝ)
  rw [hxy]
  change (integerRealMatrix N).det⁻¹ *
    (integerRealMatrix N).cramer (integerRealVector b) j=_
  rw [Matrix.cramer_apply,← hcast,← hnum]
  simp only [div_eq_mul_inv,mul_comm]

#print axioms integer_square_system_sharp_certificate
end
end Reference.IV04SharpActiveCramer
