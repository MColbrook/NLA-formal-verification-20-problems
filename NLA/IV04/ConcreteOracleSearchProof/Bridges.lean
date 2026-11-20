module

public import NLA.IV04.ConcreteOracleSearchDefinitions
public import NLA.IV04.InequalityFeasibilityBridges

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
theorem verifier_frozen (input : List Bool) :
    Reference.IV04ConcreteOracleSearch.polynomialInequalitySystemVerifier input=
      IV04.Paper.Computational.polynomialInequalitySystemVerifier input := by
  exact congrFun IV04.Paper.InequalityVerifier.polynomialInequalitySystemVerifier_frozen input
theorem accepted_certificate_frozen (instanceCode certificate : List Bool) :
    Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode certificate ↔
      IV04.Paper.Computational.polynomialInequalitySystemVerifier (Complexity.pair instanceCode certificate)=[true] := by
  unfold Reference.IV04ConcreteOracleSearch.acceptedCertificate
  rw [verifier_frozen]
theorem instance_code_frozen {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b=
      IV04.Paper.InequalityCertificate.integerMatrixInstanceCode A b := by rfl
theorem instance_polynomial_frozen : Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial=
    IV04.Paper.InequalityCertificate.inequalityInstanceLengthPolynomial := by rfl
theorem realMatrix_frozen {ι κ : Type*} (M : Matrix ι κ ℚ) :
    Reference.IV04ConcreteOracleSearch.realMatrix M=Reference.IV04AffinePolyhedronSteps.realMatrix M := by rfl
theorem realVector_frozen {ι : Type*} (b : ι → ℚ) :
    Reference.IV04ConcreteOracleSearch.realVector b=Reference.IV04AffinePolyhedronSteps.realVector b := by rfl
theorem integerRealMatrix_frozen {ι κ : Type*} (M : Matrix ι κ ℤ) :
    Reference.IV04ConcreteOracleSearch.integerRealMatrix M=Reference.IV04AffinePolyhedronSteps.integerRealMatrix M := by rfl
theorem integerRealVector_frozen {ι : Type*} (b : ι → ℤ) :
    Reference.IV04ConcreteOracleSearch.integerRealVector b=Reference.IV04AffinePolyhedronSteps.integerRealVector b := by rfl
#print axioms verifier_frozen
#print axioms accepted_certificate_frozen
#print axioms instance_code_frozen
#print axioms instance_polynomial_frozen
#print axioms realMatrix_frozen
#print axioms realVector_frozen
#print axioms integerRealMatrix_frozen
#print axioms integerRealVector_frozen
end Reference.IV04ConcreteOracleSearchProof
