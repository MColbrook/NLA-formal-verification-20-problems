module

public import NLA.IV04.ConcreteOracleSearchProof.OptimumCertificate

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
open Complexity IV04.Paper.InequalityCertificate IV04.Paper.InequalityFeasibilityNP
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem selfReduce_query_caps (instanceCode : List Bool) (bound fuel : ℕ)
    (stem : List Bool) (hcap : bound≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial instanceCode.length) :
    Reference.IV04ConcreteOracleSearch.queryCapsValid (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound fuel stem) := by
  induction fuel generalizing stem with
  | zero => simp [Reference.IV04ConcreteOracleSearch.selfReduce,Reference.IV04ConcreteOracleSearch.queryCapsValid]
  | succ fuel ih =>
    unfold Reference.IV04ConcreteOracleSearch.selfReduce
    split_ifs
    · trivial
    · exact ⟨hcap,fun answer => ih _⟩

theorem cappedBinarySearch_query_caps {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (bound fuel : ℕ) (lower upper : ℚ)
    (hcap : bound≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length) :
    Reference.IV04ConcreteOracleSearch.queryCapsValid (Reference.IV04ConcreteOracleSearch.cappedBinarySearch A b j bound fuel lower upper) := by
  induction fuel generalizing lower upper with
  | zero => trivial
  | succ fuel ih =>
    refine ⟨hcap.trans (Reference.IV04ConcreteOracleSearchProof.instance_polynomial_mono _ _
      (Reference.IV04ConcreteOracleSearchProof.original_instance_length_le_threshold A b j ((lower+upper)/2))),?_⟩
    intro answer
    cases answer <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> apply ih

theorem bindProgram_query_caps {α β : Type} (program : Reference.IV04ConcreteOracleSearch.QueryProgram α)
    (f : α → Reference.IV04ConcreteOracleSearch.QueryProgram β) (hp : Reference.IV04ConcreteOracleSearch.queryCapsValid program) (hf : ∀ a, Reference.IV04ConcreteOracleSearch.queryCapsValid (f a)) :
    Reference.IV04ConcreteOracleSearch.queryCapsValid (Reference.IV04ConcreteOracleSearch.bindProgram program f) := by
  induction program with
  | done a => exact hf a
  | ask q next ih => exact ⟨hp.1,fun answer => ih answer (hp.2 answer)⟩

theorem coordinateRecovery_query_caps {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n)
    (bound fuel : ℕ) (lower upper : ℚ)
    (hcap : bound≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length) :
    Reference.IV04ConcreteOracleSearch.queryCapsValid (Reference.IV04ConcreteOracleSearch.coordinateRecovery A b j bound fuel lower upper) := by
  apply Reference.IV04ConcreteOracleSearchProof.bindProgram_query_caps
  · exact Reference.IV04ConcreteOracleSearchProof.cappedBinarySearch_query_caps _ _ _ _ _ _ _ hcap
  · intro bracket
    apply Reference.IV04ConcreteOracleSearchProof.bindProgram_query_caps
    · exact Reference.IV04ConcreteOracleSearchProof.selfReduce_query_caps _ _ _ _ (hcap.trans (Reference.IV04ConcreteOracleSearchProof.instance_polynomial_mono _ _
        (Reference.IV04ConcreteOracleSearchProof.original_instance_length_le_threshold A b j bracket.1)))
    · intro result
      trivial

theorem executeActualNP_exact {α : Type} (program : Reference.IV04ConcreteOracleSearch.QueryProgram α) (hcap : Reference.IV04ConcreteOracleSearch.queryCapsValid program) :
    Reference.IV04ConcreteOracleSearch.executeActualNP program=Reference.IV04ConcreteOracleSearch.executeCounting program := by
  classical
  induction program with
  | done a => rfl
  | ask q next ih =>
    have ha : decide (Reference.IV04ConcreteOracleSearch.encodedQuery q∈Reference.IV04ConcreteOracleSearch.cappedPrefixFeasibilityLanguage)=decide (Reference.IV04ConcreteOracleSearch.prefixMembership q) := by
      rw [Reference.IV04ConcreteOracleSearchProof.actual_query_membership_exact q hcap.1]
    simp only [Reference.IV04ConcreteOracleSearch.executeActualNP,Reference.IV04ConcreteOracleSearch.executeCounting,ha,ih _ (hcap.2 _)]

theorem actual_np_bounded_coordinate_recovery {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) (j : Fin n)
    (hne : ∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x)
    (hline : lineFree (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b)) (upper : ℝ)
    (hupper : ∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤upper) :
    let bound := Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length
    ∃ maximum : ℚ, (Reference.IV04ConcreteOracleSearch.executeActualNP (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)).1=some maximum ∧
      (∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x ∧ x j=(maximum : ℝ)) ∧
      (∀ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x → x j≤(maximum : ℝ)) ∧
      (Reference.IV04ConcreteOracleSearch.executeActualNP (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j bound)).2≤4*bound+2 := by
  obtain ⟨maximum,he,hattain,hmax,hcount⟩ := Reference.IV04ConcreteOracleSearchProof.actual_bounded_coordinate_recovery A b hm j hne hline upper hupper
  have hcaps : Reference.IV04ConcreteOracleSearch.queryCapsValid (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j
      (Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length)) := by
    apply Reference.IV04ConcreteOracleSearchProof.coordinateRecovery_query_caps
    exact le_refl _
  have hnp := Reference.IV04ConcreteOracleSearchProof.executeActualNP_exact (Reference.IV04ConcreteOracleSearch.boundedCoordinateRecovery A b j _) hcaps
  dsimp only
  rw [hnp]
  exact ⟨maximum,(Reference.IV04ConcreteOracleSearchProof.executeCounting_result _).trans he,hattain,hmax,hcount⟩

#print axioms selfReduce_query_caps

#print axioms cappedBinarySearch_query_caps

#print axioms bindProgram_query_caps

#print axioms coordinateRecovery_query_caps

#print axioms executeActualNP_exact

#print axioms actual_np_bounded_coordinate_recovery
end Reference.IV04ConcreteOracleSearchProof
