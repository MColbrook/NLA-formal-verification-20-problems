module

public import NLA.IV04.PolyhedronSupportReplayR3.PureDefinitions
/- Rational extreme points of the original signed-orthant inequalities. -/
public import NLA.IV04.PolyhedronSupportReplayR3.AffinePolyhedronSteps.RationalVertex

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

theorem realMatrix_rationalWithOrthant {ι : Type*} {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (s : Fin n → ℚ) :
    realMatrix (rationalWithOrthant A s)=withOrthant (realMatrix A) (realVector s) := by
  classical
  ext i j
  cases i with
  | inl i => rfl
  | inr i => by_cases h : i=j <;> simp [realMatrix,rationalWithOrthant,withOrthant,realVector,h]

theorem realVector_rationalWithOrthantBounds {ι : Type*} {n : ℕ} (b : ι → ℚ) :
    realVector (rationalWithOrthantBounds (n:=n) b)=withOrthantBounds (realVector b) := by
  funext i
  cases i <;> simp [realVector,rationalWithOrthantBounds,withOrthantBounds]

theorem exists_rational_signed_orthant_extreme_point
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (s : Fin n → ℚ)
    (hs : ∀ j, s j ≠ 0)
    (hne : (signedFeasibleSet (realMatrix A) (realVector b) (realVector s)).Nonempty) :
    ∃ q : Fin n → ℚ, realVector q ∈
      (signedFeasibleSet (realMatrix A) (realVector b) (realVector s)).extremePoints ℝ := by
  classical
  have heq : feasibleSet (realMatrix (rationalWithOrthant A s))
      (realVector (rationalWithOrthantBounds b))=
      signedFeasibleSet (realMatrix A) (realVector b) (realVector s) := by
    rw [realMatrix_rationalWithOrthant,realVector_rationalWithOrthantBounds]
    ext x
    exact feasible_withOrthant_iff _ _ _ x
  have hsR : ∀ j, realVector s j ≠ 0 := by
    intro j
    change (s j : ℝ) ≠ 0
    exact_mod_cast hs j
  have hline : lineFree (realMatrix (rationalWithOrthant A s))
      (realVector (rationalWithOrthantBounds b)) := by
    rw [realMatrix_rationalWithOrthant,realVector_rationalWithOrthantBounds]
    exact signed_orthant_lineFree _ _ _ hsR
  have hnonempty : ∃ x, feasible (realMatrix (rationalWithOrthant A s))
      (realVector (rationalWithOrthantBounds b)) x := by
    simpa only [← heq,Set.Nonempty,feasibleSet,Set.mem_ofPred_eq] using hne
  obtain ⟨q,hq⟩ := exists_rational_extreme_point_of_lineFree
    (rationalWithOrthant A s) (rationalWithOrthantBounds b) hnonempty hline
  exact ⟨q,heq ▸ hq⟩

#print axioms realMatrix_rationalWithOrthant
#print axioms realVector_rationalWithOrthantBounds
#print axioms exists_rational_signed_orthant_extreme_point
end
end Reference.IV04AffinePolyhedronSteps
