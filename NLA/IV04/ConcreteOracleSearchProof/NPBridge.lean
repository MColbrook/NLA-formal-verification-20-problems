module

public import NLA.IV04.ConcreteOracleSearchProof.Recovery
public import NLA.IV04.InequalityFeasibilityCappedPrefixNP
public import NLA.IV04.InequalityFeasibilitySolution

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
open Complexity IV04.Paper.InequalityCertificate IV04.Paper.InequalityFeasibilityNP
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem actual_query_language_np : Reference.IV04ConcreteOracleSearch.cappedPrefixFeasibilityLanguage∈NP :=
  IV04.Paper.InequalityFeasibility.verified_capped_prefix_language_mem_np

theorem actual_query_membership_exact (q : Reference.IV04ConcreteOracleSearch.PrefixQuery)
    (hbound : q.bound≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial q.instanceCode.length) :
    Reference.IV04ConcreteOracleSearch.encodedQuery q∈Reference.IV04ConcreteOracleSearch.cappedPrefixFeasibilityLanguage ↔ Reference.IV04ConcreteOracleSearch.prefixMembership q := by
  exact IV04.Paper.InequalityFeasibility.verified_unary_capped_prefix_query_exact q.instanceCode q.stem q.bound hbound

theorem instance_polynomial_mono (lower upper : ℕ) (h : lower≤upper) :
    Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial lower≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial upper := by
  unfold Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial
  apply Nat.mul_le_mul (by omega)
  have hs := Nat.mul_le_mul h h
  nlinarith

theorem capped_threshold_query_actual_np_membership {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (j : Fin n) (r : ℚ)
    (bound : ℕ) (hbound : bound≤ Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b).length) :
    Reference.IV04ConcreteOracleSearch.encodedQuery (Reference.IV04ConcreteOracleSearch.cappedThresholdQuery A b j r bound)∈Reference.IV04ConcreteOracleSearch.cappedPrefixFeasibilityLanguage ↔
      Reference.IV04ConcreteOracleSearch.prefixMembership (Reference.IV04ConcreteOracleSearch.cappedThresholdQuery A b j r bound) := by
  apply Reference.IV04ConcreteOracleSearchProof.actual_query_membership_exact
  exact hbound.trans (Reference.IV04ConcreteOracleSearchProof.instance_polynomial_mono _ _ (Reference.IV04ConcreteOracleSearchProof.original_instance_length_le_threshold A b j r))

theorem encoded_query_length (q : Reference.IV04ConcreteOracleSearch.PrefixQuery) :
    (Reference.IV04ConcreteOracleSearch.encodedQuery q).length=2*q.instanceCode.length+2*q.bound+q.stem.length+4 := by
  simp [Reference.IV04ConcreteOracleSearch.encodedQuery,pair_length]
  omega

#print axioms actual_query_language_np

#print axioms actual_query_membership_exact

#print axioms instance_polynomial_mono

#print axioms capped_threshold_query_actual_np_membership

#print axioms encoded_query_length
end Reference.IV04ConcreteOracleSearchProof
