module

/- The actual bounded original objective attains a sharp-size original vertex. -/
public import NLA.IV04.SharpActiveCramer.Vertices

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04SharpActiveCramer
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment

theorem integer_original_extreme_objective_attained_sharp_size
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (H : ℕ)
    (hA : ∀ i j, |A i j|≤(H : ℤ)) (hb : ∀ i, |b i|≤(H : ℤ))
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (B : ℝ)
    (hne : ∃ x, feasible (integerRealMatrix A) (integerRealVector b) x)
    (hline : lineFree (integerRealMatrix A) (integerRealVector b))
    (hB : ∀ z, feasible (integerRealMatrix A) (integerRealVector b) z → ℓ z≤B) :
    ∃ q : Fin n → ℚ,
      realVector q ∈ (feasibleSet (integerRealMatrix A) (integerRealVector b)).extremePoints ℝ ∧
      (∀ z, feasible (integerRealMatrix A) (integerRealVector b) z → ℓ z≤ℓ (realVector q)) ∧
      ∀ j, (q j).den≤sharpCertificateBound n H ∧
        (q j).num.natAbs≤sharpCertificateBound n H := by
  obtain ⟨r,hr,hmax,_⟩ := integer_original_extreme_objective_attained_with_size
    A b H hA hb ℓ B hne hline hB
  obtain ⟨q,hqr,hqsize⟩ := integer_extreme_point_sharp_reduced_certificate
    A b (realVector r) H hA hb hr
  exact ⟨q,hqr.symm ▸ hr,by simpa only [hqr] using hmax,hqsize⟩

#print axioms integer_original_extreme_objective_attained_sharp_size
end
end Reference.IV04SharpActiveCramer
