module

public import NLA.IV04.PolyhedronSupportReplayR3.PureDefinitions
/- Original integer polyhedra attain bounded objectives at rational vertices with reduced size bounds. -/
public import NLA.IV04.PolyhedronSupportReplayR3.OriginalObjectiveAttainment.RationalDenominator

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps

theorem realMatrix_integerRationalMatrix {ι κ : Type*} (A : Matrix ι κ ℤ) :
    realMatrix (integerRationalMatrix A)=integerRealMatrix A := by
  ext i j
  change ((A i j : ℚ) : ℝ)=(A i j : ℝ)
  norm_cast

theorem realVector_integerRationalVector {ι : Type*} (b : ι → ℤ) :
    realVector (integerRationalVector b)=integerRealVector b := by
  funext i
  change ((b i : ℚ) : ℝ)=(b i : ℝ)
  norm_cast

theorem integer_original_extreme_objective_attained_with_size
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (H : ℕ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ))
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (B : ℝ)
    (hne : ∃ x, feasible (integerRealMatrix A) (integerRealVector b) x)
    (hline : lineFree (integerRealMatrix A) (integerRealVector b))
    (hB : ∀ z, feasible (integerRealMatrix A) (integerRealVector b) z → ℓ z ≤ B) :
    ∃ q : Fin n → ℚ,
      realVector q ∈ (feasibleSet (integerRealMatrix A) (integerRealVector b)).extremePoints ℝ ∧
      (∀ z, feasible (integerRealMatrix A) (integerRealVector b) z → ℓ z ≤ ℓ (realVector q)) ∧
      ∀ j, (q j).den ≤ gramCertificateBound (Fintype.card ι) n H ∧
        (q j).num.natAbs ≤ gramCertificateBound (Fintype.card ι) n H := by
  have hneQ : ∃ x, feasible (realMatrix (integerRationalMatrix A))
      (realVector (integerRationalVector b)) x := by
    simpa only [realMatrix_integerRationalMatrix,realVector_integerRationalVector] using hne
  have hlineQ : lineFree (realMatrix (integerRationalMatrix A))
      (realVector (integerRationalVector b)) := by
    simpa only [realMatrix_integerRationalMatrix,realVector_integerRationalVector] using hline
  have hBQ : ∀ z, feasible (realMatrix (integerRationalMatrix A))
      (realVector (integerRationalVector b)) z → ℓ z ≤ B := by
    simpa only [realMatrix_integerRationalMatrix,realVector_integerRationalVector] using hB
  obtain ⟨q,hq,hkernel,hmax⟩ := rational_original_extreme_objective_attained
    (integerRationalMatrix A) (integerRationalVector b) ℓ B hneQ hlineQ hBQ
  rw [realMatrix_integerRationalMatrix,realVector_integerRationalVector] at hq hkernel hmax
  obtain ⟨p,d,hd,hdQ,hpQ,hcoords⟩ := integer_tight_common_denominator_certificate
    A b (realVector q) H hA hb hkernel
  have hfrac (j : Fin n) : q j=(p j : ℚ)/(d : ℚ) := by
    have hj := hcoords j
    change (q j : ℝ)=(p j : ℝ)/(d : ℝ) at hj
    exact_mod_cast hj
  refine ⟨q,hq,hmax,?_⟩
  intro j
  exact ⟨rational_den_le_of_integer_fraction (q j) (p j) d _ hd (hfrac j) hdQ,
    rational_num_natAbs_le_of_integer_fraction (q j) (p j) d _ hd (hfrac j) (hpQ j)⟩

#print axioms realMatrix_integerRationalMatrix
#print axioms realVector_integerRationalVector
#print axioms integer_original_extreme_objective_attained_with_size
end
end Reference.IV04OriginalObjectiveAttainment
