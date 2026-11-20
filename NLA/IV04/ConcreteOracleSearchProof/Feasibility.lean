module

public import NLA.IV04.ConcreteOracleSearchProof.SelfReduction
public import NLA.IV04.ConcreteOracleSearchProof.Bridges

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
open IV04.Paper.InequalityCertificate Reference.IV04AffinePolyhedronSteps
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem actual_feasibility_certificate_search {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m)
    (hne : ∃ x, feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b) x) :
    let instanceCode := Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b
    let bound := Reference.IV04ConcreteOracleSearch.inequalityInstanceLengthPolynomial instanceCode.length
    Reference.IV04ConcreteOracleSearch.queriesAtMost bound (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound bound []) ∧
    ∃ certificate, Reference.IV04ConcreteOracleSearch.execute (Reference.IV04ConcreteOracleSearch.selfReduce instanceCode bound bound [])=some certificate ∧
      certificate.length≤bound ∧ Reference.IV04ConcreteOracleSearch.acceptedCertificate instanceCode certificate := by
  apply Reference.IV04ConcreteOracleSearchProof.bounded_certificate_self_reduction
  simp only [Reference.IV04ConcreteOracleSearchProof.accepted_certificate_frozen]
  exact (real_feasible_iff_arbitrary_bounded_certificate A b hm).mp hne

#print axioms actual_feasibility_certificate_search
end Reference.IV04ConcreteOracleSearchProof
