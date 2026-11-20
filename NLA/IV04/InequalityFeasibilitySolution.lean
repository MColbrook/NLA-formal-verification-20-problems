module

public import NLA.IV04.InequalityFeasibilityBridges

@[expose] public section
set_option autoImplicit false
open Complexity
namespace IV04.Paper.InequalityFeasibility
theorem verified_bounded_verifier_mem_fp : boundedInequalityVerifier ∈ FP := by rw [bounded_verifier_frozen];exact IV04.Paper.InequalityFeasibilityNP.bounded_inequality_verifier_mem_fp

theorem verified_bounded_verifier_exact (input : List Bool) : boundedInequalityVerifier input=[true] ↔ InequalityVerifier.polynomialInequalitySystemVerifier input=[true] ∧ (pairSnd input).length≤ inequalityInstanceLengthPolynomial (pairFst input).length := by simpa only [bounded_verifier_frozen,InequalityVerifier.polynomialInequalitySystemVerifier_frozen,certificate_bound_frozen] using IV04.Paper.InequalityFeasibilityNP.bounded_inequality_verifier_exact input

theorem verified_integer_language_exact (inputCode : List Bool) : inputCode ∈ integerFeasibilityLanguage ↔ ∃ certificate : List Bool, certificate.length≤ inequalityInstanceLengthPolynomial inputCode.length ∧ InequalityVerifier.polynomialInequalitySystemVerifier (pair inputCode certificate)=[true] := by simpa only [integer_feasibility_language_frozen,certificate_bound_frozen,InequalityVerifier.polynomialInequalitySystemVerifier_frozen] using IV04.Paper.InequalityFeasibilityNP.integer_feasibility_iff_bounded_binary_certificate inputCode

theorem verified_integer_language_mem_np : integerFeasibilityLanguage ∈ NP := by rw [integer_feasibility_language_frozen];exact IV04.Paper.InequalityFeasibilityNP.integer_feasibility_language_mem_np

theorem verified_canonical_integer_language_exact {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) : canonicalIntegerMatrixInstanceCode A b ∈ integerFeasibilityLanguage ↔ ∃ x, integerRealFeasible A b x := by simpa only [canonical_integer_matrix_code_frozen,integer_feasibility_language_frozen,integer_real_feasible_frozen] using IV04.Paper.InequalityFeasibilityNP.canonical_integer_matrix_language_exact A b

theorem verified_prefix_verifier_mem_fp : prefixInequalityVerifier ∈ FP := by rw [prefix_verifier_frozen];exact IV04.Paper.InequalityFeasibilityNP.prefix_inequality_verifier_mem_fp

theorem verified_prefix_language_mem_np : prefixFeasibilityLanguage ∈ NP := by rw [prefix_feasibility_language_frozen];exact IV04.Paper.InequalityFeasibilityNP.prefix_feasibility_language_mem_np

theorem verified_prefix_query_exact (inputCode initialBits : List Bool) : pair inputCode initialBits ∈ prefixFeasibilityLanguage ↔ ∃ tail : List Bool, (initialBits++tail).length≤ inequalityInstanceLengthPolynomial inputCode.length ∧ InequalityVerifier.polynomialInequalitySystemVerifier (pair inputCode (initialBits++tail))=[true] := by simpa only [prefix_feasibility_language_frozen,certificate_bound_frozen,InequalityVerifier.polynomialInequalitySystemVerifier_frozen] using IV04.Paper.InequalityFeasibilityNP.prefix_query_exact inputCode initialBits

theorem verified_prefix_empty_exact (inputCode : List Bool) : pair inputCode [] ∈ prefixFeasibilityLanguage ↔ inputCode ∈ integerFeasibilityLanguage := by simpa only [prefix_feasibility_language_frozen,integer_feasibility_language_frozen] using IV04.Paper.InequalityFeasibilityNP.prefix_empty_iff_integer_feasibility inputCode

theorem verified_capped_prefix_verifier_mem_fp : cappedPrefixInequalityVerifier ∈ FP := by rw [capped_prefix_verifier_frozen];exact IV04.Paper.InequalityFeasibilityNP.capped_prefix_inequality_verifier_mem_fp

theorem verified_capped_prefix_language_mem_np : cappedPrefixFeasibilityLanguage ∈ NP := by rw [capped_prefix_feasibility_language_frozen];exact IV04.Paper.InequalityFeasibilityNP.capped_prefix_feasibility_language_mem_np

theorem verified_capped_prefix_query_exact (inputCode ruler initialBits : List Bool) : pair inputCode (pair ruler initialBits) ∈ cappedPrefixFeasibilityLanguage ↔ ∃ tail : List Bool, (initialBits++tail).length≤ruler.length ∧ (initialBits++tail).length≤ inequalityInstanceLengthPolynomial inputCode.length ∧ InequalityVerifier.polynomialInequalitySystemVerifier (pair inputCode (initialBits++tail))=[true] := by simpa only [capped_prefix_feasibility_language_frozen,certificate_bound_frozen,InequalityVerifier.polynomialInequalitySystemVerifier_frozen] using IV04.Paper.InequalityFeasibilityNP.capped_prefix_query_exact inputCode ruler initialBits

theorem verified_unary_capped_prefix_query_exact (inputCode initialBits : List Bool) (B : ℕ) (hB : B≤ inequalityInstanceLengthPolynomial inputCode.length) : pair inputCode (pair (List.replicate B true) initialBits) ∈ cappedPrefixFeasibilityLanguage ↔ ∃ tail : List Bool, (initialBits++tail).length≤B ∧ InequalityVerifier.polynomialInequalitySystemVerifier (pair inputCode (initialBits++tail))=[true] := by simpa only [capped_prefix_feasibility_language_frozen,certificate_bound_frozen,InequalityVerifier.polynomialInequalitySystemVerifier_frozen] using IV04.Paper.InequalityFeasibilityNP.unary_capped_prefix_query_exact inputCode initialBits B hB
#print axioms verified_bounded_verifier_mem_fp
#print axioms verified_bounded_verifier_exact
#print axioms verified_integer_language_exact
#print axioms verified_integer_language_mem_np
#print axioms verified_canonical_integer_language_exact
#print axioms verified_prefix_verifier_mem_fp
#print axioms verified_prefix_language_mem_np
#print axioms verified_prefix_query_exact
#print axioms verified_prefix_empty_exact
#print axioms verified_capped_prefix_verifier_mem_fp
#print axioms verified_capped_prefix_language_mem_np
#print axioms verified_capped_prefix_query_exact
#print axioms verified_unary_capped_prefix_query_exact
end IV04.Paper.InequalityFeasibility
