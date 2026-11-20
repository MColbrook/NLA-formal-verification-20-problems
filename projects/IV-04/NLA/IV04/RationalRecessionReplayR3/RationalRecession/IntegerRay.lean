module

public import NLA.IV04.RationalRecessionReplayR3.PureDefinitions
/- Honest augmented-matrix reduced size bound for an actual rational recession direction. -/
public import NLA.IV04.RationalRecessionReplayR3.RationalRecession.MaskSize

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04RationalRecessionRay
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment

theorem integer_unbounded_objective_has_sized_rational_recession
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℤ) (b : ι → ℤ) (c : Fin n → ℤ) (H : ℕ)
    (hA : ∀ i j, |A i j| ≤ (H : ℤ)) (hc : ∀ j, |c j| ≤ (H : ℤ)) (hH : 1 ≤ H)
    (hline : lineFree (integerRealMatrix A) (integerRealVector b))
    (hunbounded : ∀ K : ℕ, ∃ x, feasible (integerRealMatrix A) (integerRealVector b) x ∧
      (K : ℝ) ≤ rowObjective (integerRealVector c) x) :
    ∃ r : Fin n → ℚ, r ≠ 0 ∧ (∀ i, (integerRealMatrix A *ᵥ realVector r) i ≤ 0) ∧
      1 ≤ rowObjective (integerRealVector c) (realVector r) ∧
      ∀ j, (r j).den ≤ gramCertificateBound (Fintype.card ι+1) n H ∧
        (r j).num.natAbs ≤ gramCertificateBound (Fintype.card ι+1) n H := by
  classical
  have hlineQ : lineFree (realMatrix (integerRationalMatrix A))
      (realVector (integerRationalVector b)) := by
    simpa only [realMatrix_integerRationalMatrix,realVector_integerRationalVector] using hline
  have huQ : ∀ K : ℕ, ∃ x, feasible (realMatrix (integerRationalMatrix A))
      (realVector (integerRationalVector b)) x ∧
      (K : ℝ) ≤ rowObjective (realVector (integerRationalVector c)) x := by
    simpa only [realMatrix_integerRationalMatrix,realVector_integerRationalVector] using hunbounded
  obtain ⟨I,r,hr,hrne,hdir,hpos⟩ := unbounded_objective_has_rational_recession_mask
    (integerRationalMatrix A) (integerRationalVector b) (integerRationalVector c) hlineQ huQ
  have haug : integerRationalMatrix (integerThresholdMatrix A c)=
      thresholdMatrix (integerRationalMatrix A) (integerRationalVector c) := by
    ext i j
    cases i with
    | inl i => rfl
    | inr u => simp [integerRationalMatrix,integerThresholdMatrix,thresholdMatrix,integerRationalVector]
  have hderiv : integerRationalVector (integerThresholdDerivativeBounds (ι:=ι))=
      thresholdDerivativeBounds := by
    funext i
    cases i <;> simp [integerRationalVector,integerThresholdDerivativeBounds,thresholdDerivativeBounds]
  have hrQ : r=originalMaskCandidate (integerRationalMatrix (integerThresholdMatrix A c))
      (integerRationalVector integerThresholdDerivativeBounds) I := by
    rw [haug,hderiv]
    exact hr
  have haugH : ∀ i j, |integerThresholdMatrix A c i j| ≤ (H : ℤ) := by
    intro i j
    cases i with
    | inl i => exact hA i j
    | inr u => simpa [integerThresholdMatrix] using hc j
  have hderivH : ∀ i : ι ⊕ Unit, |integerThresholdDerivativeBounds i| ≤ (H : ℤ) := by
    intro i
    cases i with
    | inl i => simp [integerThresholdDerivativeBounds]
    | inr u =>
        have hh : (1 : ℤ) ≤ (H : ℤ) := by exact_mod_cast hH
        simpa [integerThresholdDerivativeBounds] using hh
  have hsize := integer_mask_candidate_reduced_size (integerThresholdMatrix A c)
    integerThresholdDerivativeBounds I H haugH hderivH (hrQ ▸ hrne)
  rw [← hrQ] at hsize
  refine ⟨r,hrne,?_,?_,?_⟩
  · simpa only [realMatrix_integerRationalMatrix] using hdir
  · simpa only [realVector_integerRationalVector] using hpos
  · simpa using hsize

#print axioms integer_unbounded_objective_has_sized_rational_recession
end
end Reference.IV04RationalRecessionRay
