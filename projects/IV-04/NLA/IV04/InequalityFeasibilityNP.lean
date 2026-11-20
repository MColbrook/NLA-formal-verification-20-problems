module

public import NLA.IV04.InequalityFeasibilityWordWitness
public import NLA.IV04.InequalityFeasibilityBoundedVerifier

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational Reference.IV04AffinePolyhedronSteps
open scoped Matrix
namespace IV04.Paper.InequalityFeasibilityNP
open IV04.Paper.InequalityCertificate

theorem integer_feasibility_iff_actual_fp_verifier (inputCode : List Bool) :
    inputCode ∈ integerFeasibilityLanguage ↔
      ∃ certificate : List Bool, pair inputCode certificate ∈ boundedInequalityVerifierLanguage := by
  rw [integer_feasibility_iff_bounded_binary_certificate]
  apply exists_congr
  intro certificate
  exact and_comm.trans (bounded_inequality_verifier_pair inputCode certificate).symm

theorem integer_feasibility_language_mem_np : integerFeasibilityLanguage ∈ NP :=
  mem_NP_of_poly_witness certificateLengthPolynomial
    bounded_inequality_verifier_language_mem_p bounded_inequality_verifier_balanced
    integer_feasibility_iff_actual_fp_verifier

theorem canonical_integer_matrix_language_exact {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    integerMatrixInstanceCode A b ∈ integerFeasibilityLanguage ↔
      ∃ x, feasible (integerRealMatrix A) (integerRealVector b) x := by
  rw [integer_feasibility_iff_bounded_binary_certificate]
  exact (real_feasible_iff_binary_certificate_all_rows A b).symm

theorem integer_feasibility_actual_np_and_fp :
    integerFeasibilityLanguage ∈ NP ∧ boundedInequalityVerifier ∈ FP ∧
    (∀ inputCode : List Bool, inputCode ∈ integerFeasibilityLanguage ↔
      ∃ certificate : List Bool,
        certificate.length≤ inequalityInstanceLengthPolynomial inputCode.length ∧
        polynomialInequalitySystemVerifier (pair inputCode certificate)=[true]) :=
  ⟨integer_feasibility_language_mem_np,bounded_inequality_verifier_mem_fp,
    integer_feasibility_iff_bounded_binary_certificate⟩

#print axioms integer_feasibility_iff_actual_fp_verifier
#print axioms integer_feasibility_language_mem_np
#print axioms canonical_integer_matrix_language_exact
#print axioms integer_feasibility_actual_np_and_fp
end IV04.Paper.InequalityFeasibilityNP
