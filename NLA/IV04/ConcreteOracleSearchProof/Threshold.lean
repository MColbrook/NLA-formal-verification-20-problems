module

public import NLA.IV04.ConcreteOracleSearchProof.Feasibility

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
open IV04.Paper.InequalityCertificate Reference.IV04AffinePolyhedronSteps
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem threshold_feasible_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (j : Fin n) (r : ℚ) (x : Fin n → ℝ) :
    feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r)) (Reference.IV04ConcreteOracleSearch.integerRealVector (Reference.IV04ConcreteOracleSearch.thresholdBounds b r)) x ↔
      feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x ∧ (r : ℝ)≤x j := by
  have hd : (0 : ℝ)<(r.den : ℝ) := by exact_mod_cast r.pos
  have hrow : (Reference.IV04ConcreteOracleSearch.integerRealMatrix (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r) *ᵥ x) 0=
      -(r.den : ℝ)*x j := by
    simp [Reference.IV04ConcreteOracleSearch.integerRealMatrix,Reference.IV04ConcreteOracleSearch.thresholdMatrix,Matrix.mulVec,dotProduct]
  constructor
  · intro hx
    refine ⟨fun i => ?_,?_⟩
    · simpa [Reference.IV04ConcreteOracleSearch.integerRealMatrix,Reference.IV04ConcreteOracleSearch.integerRealVector,Reference.IV04ConcreteOracleSearch.thresholdMatrix,Reference.IV04ConcreteOracleSearch.thresholdBounds,
        Matrix.mulVec,dotProduct] using hx i.succ
    · have hzero := hx 0
      rw [hrow] at hzero
      simp only [Reference.IV04ConcreteOracleSearch.integerRealVector,Reference.IV04ConcreteOracleSearch.thresholdBounds,Fin.cases_zero,Int.cast_neg] at hzero
      rw [Rat.cast_def,div_le_iff₀ hd]
      nlinarith
  · rintro ⟨hx,hr⟩
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hrow]
      simp only [Reference.IV04ConcreteOracleSearch.integerRealVector,Reference.IV04ConcreteOracleSearch.thresholdBounds,Fin.cases_zero,Int.cast_neg]
      rw [Rat.cast_def,div_le_iff₀ hd] at hr
      nlinarith
    · simpa [Reference.IV04ConcreteOracleSearch.integerRealMatrix,Reference.IV04ConcreteOracleSearch.integerRealVector,Reference.IV04ConcreteOracleSearch.thresholdMatrix,Reference.IV04ConcreteOracleSearch.thresholdBounds,
        Matrix.mulVec,dotProduct] using hx i

theorem threshold_query_membership_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n) (r : ℚ) :
    Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.thresholdQuery A b j r) ↔
      ∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x ∧ (r : ℝ)≤x j := by
  change (∃ certificate : List Bool,
      certificate.length ≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial
        (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r) (Reference.IV04ConcreteOracleSearch.thresholdBounds b r)).length ∧
      Reference.IV04ConcreteOracleSearch.acceptedCertificate (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r) (Reference.IV04ConcreteOracleSearch.thresholdBounds b r)) certificate) ↔ _
  simp only [Reference.IV04ConcreteOracleSearchProof.accepted_certificate_frozen,
    Reference.IV04ConcreteOracleSearchProof.instance_code_frozen,
    Reference.IV04ConcreteOracleSearchProof.instance_polynomial_frozen]
  rw [← real_feasible_iff_arbitrary_bounded_certificate (Reference.IV04ConcreteOracleSearch.thresholdMatrix A j r)
    (Reference.IV04ConcreteOracleSearch.thresholdBounds b r) (by omega)]
  exact exists_congr (Reference.IV04ConcreteOracleSearchProof.threshold_feasible_iff A b j r)

theorem threshold_membership_iff_le_actual_optimum {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (x : Fin n → ℝ) (hx : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x)
    (hmax : ∀ y, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) y → y j≤x j)
    (r : ℚ) : Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.thresholdQuery A b j r) ↔ (r : ℝ)≤x j := by
  rw [Reference.IV04ConcreteOracleSearchProof.threshold_query_membership_iff]
  constructor
  · rintro ⟨y,hy,hr⟩
    exact hr.trans (hmax y hy)
  · intro hr
    exact ⟨x,hx,hr⟩

#print axioms threshold_feasible_iff

#print axioms threshold_query_membership_iff

#print axioms threshold_membership_iff_le_actual_optimum
end Reference.IV04ConcreteOracleSearchProof
