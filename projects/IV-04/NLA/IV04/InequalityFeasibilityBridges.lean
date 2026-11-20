module

public import NLA.IV04.InequalityFeasibilityDefinitions
public import NLA.IV04.InequalityFeasibilityCappedPrefixNP
public import NLA.IV04.InequalityVerifierBridges

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational
namespace IV04.Paper.InequalityFeasibility

private theorem xorSuffix_frozen : InequalityVerifier.EqualityFlags.xorSuffix = Cobham.xorSuffix := by
  funext a b
  induction a with
  | nil => rfl
  | cons bit tail ih => cases bit <;> simp only [InequalityVerifier.EqualityFlags.xorSuffix,Cobham.xorSuffix,ih]

private theorem allZeroFlag_frozen : InequalityVerifier.EqualityFlags.allZeroFlag = Cobham.allZeroFlag := by
  funext a
  induction a with
  | nil => rfl
  | cons bit tail ih => cases bit <;> simp only [InequalityVerifier.EqualityFlags.allZeroFlag,Cobham.allZeroFlag,ih]

private theorem eqFlag_frozen : InequalityVerifier.EqualityFlags.eqFlag = Cobham.eqFlag := by
  funext
  simp only [InequalityVerifier.EqualityFlags.eqFlag,Cobham.eqFlag,
    InequalityVerifier.EqualityFlags.lenEqFlag,Cobham.lenEqFlag,
    InequalityVerifier.EqualityFlags.lenLeFlag,Cobham.lenLeFlag,xorSuffix_frozen,allZeroFlag_frozen]

theorem integer_real_feasible_frozen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (x : Fin n → ℝ) :
    integerRealFeasible A b x=Reference.IV04AffinePolyhedronSteps.feasible (Reference.IV04AffinePolyhedronSteps.integerRealMatrix A) (Reference.IV04AffinePolyhedronSteps.integerRealVector b) x := rfl

theorem word_matrix_code_frozen {m n : ℕ} (A : Matrix (Fin m) (Fin n) (List Bool))
    (b : Fin m → List Bool) : wordMatrixInstanceCode A b=IV04.Paper.InequalityFeasibilityNP.wordMatrixInstanceCode A b := rfl

theorem integer_feasibility_language_frozen : integerFeasibilityLanguage=IV04.Paper.InequalityFeasibilityNP.integerFeasibilityLanguage := rfl

theorem canonical_integer_matrix_code_frozen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) : canonicalIntegerMatrixInstanceCode A b=IV04.Paper.InequalityCertificate.integerMatrixInstanceCode A b := by
  simp only [canonicalIntegerMatrixInstanceCode,IV04.Paper.InequalityCertificate.integerMatrixInstanceCode,
    InequalityVerifier.inequalityIntegerWord_frozen]
  rfl

theorem certificate_bound_frozen : inequalityInstanceLengthPolynomial=IV04.Paper.InequalityCertificate.inequalityInstanceLengthPolynomial := rfl

theorem bounded_verifier_frozen : boundedInequalityVerifier=IV04.Paper.InequalityFeasibilityNP.boundedInequalityVerifier := by
  funext input
  simp only [boundedInequalityVerifier,IV04.Paper.InequalityFeasibilityNP.boundedInequalityVerifier,
    InequalityVerifier.polynomialInequalitySystemVerifier_frozen]
  rfl

theorem bounded_verifier_language_frozen : boundedInequalityVerifierLanguage=IV04.Paper.InequalityFeasibilityNP.boundedInequalityVerifierLanguage := by
  simp only [boundedInequalityVerifierLanguage,IV04.Paper.InequalityFeasibilityNP.boundedInequalityVerifierLanguage,bounded_verifier_frozen]

theorem prefix_feasibility_language_frozen : prefixFeasibilityLanguage=IV04.Paper.InequalityFeasibilityNP.prefixFeasibilityLanguage := by
  simp only [prefixFeasibilityLanguage,IV04.Paper.InequalityFeasibilityNP.prefixFeasibilityLanguage,
    InequalityVerifier.polynomialInequalitySystemVerifier_frozen]
  rfl

theorem prefix_verifier_frozen : prefixInequalityVerifier=IV04.Paper.InequalityFeasibilityNP.prefixInequalityVerifier := by
  funext input
  simp only [prefixInequalityVerifier,IV04.Paper.InequalityFeasibilityNP.prefixInequalityVerifier,bounded_verifier_frozen,eqFlag_frozen]

theorem capped_prefix_feasibility_language_frozen : cappedPrefixFeasibilityLanguage=IV04.Paper.InequalityFeasibilityNP.cappedPrefixFeasibilityLanguage := by
  simp only [cappedPrefixFeasibilityLanguage,IV04.Paper.InequalityFeasibilityNP.cappedPrefixFeasibilityLanguage,
    InequalityVerifier.polynomialInequalitySystemVerifier_frozen]
  rfl

theorem capped_prefix_verifier_frozen : cappedPrefixInequalityVerifier=IV04.Paper.InequalityFeasibilityNP.cappedPrefixInequalityVerifier := by
  funext input
  simp only [cappedPrefixInequalityVerifier,IV04.Paper.InequalityFeasibilityNP.cappedPrefixInequalityVerifier,
    bounded_verifier_frozen,eqFlag_frozen]
  rfl
#print axioms integer_real_feasible_frozen
#print axioms word_matrix_code_frozen
#print axioms integer_feasibility_language_frozen
#print axioms canonical_integer_matrix_code_frozen
#print axioms certificate_bound_frozen
#print axioms bounded_verifier_frozen
#print axioms bounded_verifier_language_frozen
#print axioms prefix_feasibility_language_frozen
#print axioms prefix_verifier_frozen
#print axioms capped_prefix_feasibility_language_frozen
#print axioms capped_prefix_verifier_frozen
end IV04.Paper.InequalityFeasibility
