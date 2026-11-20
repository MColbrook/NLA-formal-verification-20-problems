module

public import NLA.IV04.PolyhedronSupportReplayR3.PureDefinitions
/- Bound for an actual extreme point of original integer signed-orthant inequalities. -/
public import NLA.IV04.PolyhedronSupportReplayR3.AffinePolyhedronSteps.IntegerPointedCertificate

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

theorem integerRealMatrix_withOrthant {ι : Type*} {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (s : Fin n → ℤ) :
    integerRealMatrix (integerWithOrthant A s)=
      withOrthant (integerRealMatrix A) (integerRealVector s) := by
  classical
  ext i j
  cases i with
  | inl i => rfl
  | inr i => by_cases h : i=j <;>
      simp [integerRealMatrix,integerWithOrthant,withOrthant,integerRealVector,h]

theorem integerRealVector_withOrthantBounds {ι : Type*} {n : ℕ} (b : ι → ℤ) :
    integerRealVector (integerWithOrthantBounds (n:=n) b)=withOrthantBounds (integerRealVector b) := by
  funext i
  cases i <;> simp [integerRealVector,integerWithOrthantBounds,withOrthantBounds]

theorem exists_bounded_signed_orthant_extreme_certificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (s : Fin n → ℤ) (H : ℕ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hb : ∀ i, |b i| ≤ (H : ℤ))
    (hs : ∀ j, s j ≠ 0) (hsH : ∀ j, |s j| ≤ (H : ℤ))
    (hne : (signedFeasibleSet (integerRealMatrix A) (integerRealVector b)
      (integerRealVector s)).Nonempty) :
    ∃ x : Fin n → ℝ,
      x ∈ (signedFeasibleSet (integerRealMatrix A) (integerRealVector b)
        (integerRealVector s)).extremePoints ℝ ∧
      ∃ p : Fin n → ℤ, ∃ d : ℤ,
        d ≠ 0 ∧ |d| ≤ (gramCertificateBound (Fintype.card ι+n) n H : ℤ) ∧
        (∀ j, |p j| ≤ (gramCertificateBound (Fintype.card ι+n) n H : ℤ)) ∧
        ∀ j, x j=(p j : ℝ)/(d : ℝ) := by
  classical
  have heq : feasibleSet (integerRealMatrix (integerWithOrthant A s))
      (integerRealVector (integerWithOrthantBounds b))=
      signedFeasibleSet (integerRealMatrix A) (integerRealVector b) (integerRealVector s) := by
    rw [integerRealMatrix_withOrthant,integerRealVector_withOrthantBounds]
    ext x
    exact feasible_withOrthant_iff _ _ _ x
  have hsR : ∀ j, integerRealVector s j ≠ 0 := by
    intro j
    change (s j : ℝ) ≠ 0
    exact_mod_cast hs j
  have hline : lineFree (integerRealMatrix (integerWithOrthant A s))
      (integerRealVector (integerWithOrthantBounds b)) := by
    rw [integerRealMatrix_withOrthant,integerRealVector_withOrthantBounds]
    exact signed_orthant_lineFree _ _ _ hsR
  have hnonempty : ∃ x, feasible (integerRealMatrix (integerWithOrthant A s))
      (integerRealVector (integerWithOrthantBounds b)) x := by
    simpa only [← heq,Set.Nonempty,feasibleSet,Set.mem_ofPred_eq] using hne
  have haug : ∀ i j, |integerWithOrthant A s i j| ≤ (H : ℤ) := by
    intro i j
    cases i with
    | inl i => exact hA i j
    | inr i =>
        change |if i=j then -s i else 0| ≤ (H : ℤ)
        split_ifs
        · simpa using hsH i
        · simp
  have hbaug : ∀ i, |integerWithOrthantBounds (n:=n) b i| ≤ (H : ℤ) := by
    intro i
    cases i with
    | inl i => exact hb i
    | inr i => simp [integerWithOrthantBounds]
  obtain ⟨x,hx,hcert⟩ := exists_bounded_integer_extreme_certificate
    (integerWithOrthant A s) (integerWithOrthantBounds b) H haug hbaug hnonempty hline
  refine ⟨x,heq ▸ hx,?_⟩
  simpa using hcert

#print axioms integerRealMatrix_withOrthant
#print axioms integerRealVector_withOrthantBounds
#print axioms exists_bounded_signed_orthant_extreme_certificate
end
end Reference.IV04AffinePolyhedronSteps
