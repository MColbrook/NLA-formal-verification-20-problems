module

public import NLA.IV04.ConcreteOracleSearchProof.BinarySearch

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearchProof
open Complexity IV04.Paper.Computational IV04.Paper.InequalityCertificate
open Reference.IV04AffinePolyhedronSteps
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps
open Reference.IV04ConcreteOracleSearch

theorem payloadNth_code (words : List (List Bool)) (j : Fin words.length) :
    Reference.IV04ConcreteOracleSearch.payloadNth j.val (payloadListCode words)=words.get j := by
  induction words with
  | nil => exact Fin.elim0 j
  | cons first rest ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [Reference.IV04ConcreteOracleSearch.payloadNth,payloadListCode,pairFst_pair]
    · simpa [Reference.IV04ConcreteOracleSearch.payloadNth,payloadListCode,pairSnd_pair] using ih k

theorem natural_fraction_den_le (p : ℤ) (d : ℕ) (hd : 0<d) :
    ((p : ℚ)/(d : ℚ)).den≤d := by
  rw [show (d : ℚ)=((d : ℤ) : ℚ) by simp,← Rat.divInt_eq_div]
  apply Nat.le_of_dvd hd
  simpa using Int.natAbs_dvd_natAbs.mpr (Rat.den_dvd p (d : ℤ))

theorem accepted_certificate_point {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m)
    (certificate : List Bool) (haccept : Reference.IV04ConcreteOracleSearch.acceptedCertificate (Reference.IV04ConcreteOracleSearch.integerMatrixInstanceCode A b) certificate) :
    feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b)
      (Reference.IV04ConcreteOracleSearch.realVector (Reference.IV04ConcreteOracleSearch.certificatePoint n certificate)) ∧
      ∀ j, (Reference.IV04ConcreteOracleSearch.certificatePoint n certificate j).den≤2^certificate.length := by
  rw [Reference.IV04ConcreteOracleSearchProof.accepted_certificate_frozen] at haccept
  obtain ⟨rows,numerators,denominator,hcode,hd,hrows⟩ :=
    (inequality_system_verifier_exact _).mp haccept
  have hinst := congrArg pairFst hcode
  simp only [inequalitySystemCode,pairFst_pair] at hinst
  have hdecoded : List.ofFn (Reference.IV04ConcreteOracleSearch.integerMatrixRowCode A b)=rows := payload_code_injective hinst
  have hrow (i : Fin m) : decodedInequalityRow numerators denominator (Reference.IV04ConcreteOracleSearch.integerMatrixRowCode A b i) := by
    apply hrows
    rw [← hdecoded]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hmatrix (i : Fin m) := decoded_matrix_row_sound A b i numerators denominator (hrow i)
  have hlen : numerators.length=n := (hmatrix ⟨0,hm⟩).1.symm
  cases hlen
  have hcert := congrArg pairSnd hcode
  simp only [inequalitySystemCode,pairSnd_pair] at hcert
  have hcoord (j : Fin numerators.length) :
      Reference.IV04ConcreteOracleSearch.certificatePoint numerators.length certificate j=
        (signedWordValue (numerators.get j) : ℚ)/(wordValue denominator : ℚ) := by
    simp only [Reference.IV04ConcreteOracleSearch.certificatePoint,Reference.IV04ConcreteOracleSearch.certificateCoordinate,hcert,pairFst_pair,pairSnd_pair,
      Reference.IV04ConcreteOracleSearchProof.payloadNth_code]
  let p : Fin numerators.length → ℤ := fun j => signedWordValue (numerators.get j)
  have hp : List.ofFn p=numerators.map signedWordValue := by
    change List.ofFn (signedWordValue ∘ numerators.get)=numerators.map signedWordValue
    rw [← List.map_ofFn,List.ofFn_get]
  have hfeas : feasible (Reference.IV04ConcreteOracleSearch.integerRealMatrix A) (Reference.IV04ConcreteOracleSearch.integerRealVector b)
      (fun j => (p j : ℝ)/(wordValue denominator : ℝ)) := by
    apply (matrix_fraction_feasible_iff A b p (wordValue denominator) hd).mpr
    intro i
    have hi := (hmatrix i).2
    rw [← hp,integer_dot_ofFn] at hi
    exact hi
  have hcast : Reference.IV04ConcreteOracleSearch.realVector (Reference.IV04ConcreteOracleSearch.certificatePoint numerators.length certificate)=
      (fun j => (p j : ℝ)/(wordValue denominator : ℝ)) := by
    funext j
    simp [Reference.IV04ConcreteOracleSearch.realVector,hcoord,p]
  refine ⟨hcast.symm ▸ hfeas,?_⟩
  have hdlen : denominator.length≤certificate.length := by
    rw [hcert,pair_length]
    omega
  have hdQ : wordValue denominator≤2^certificate.length :=
    (word_value_lt_pow_length denominator).le.trans
      (Nat.pow_le_pow_right (by omega) hdlen)
  intro j
  rw [hcoord j]
  exact (Reference.IV04ConcreteOracleSearchProof.natural_fraction_den_le _ _ hd).trans hdQ

#print axioms payloadNth_code

#print axioms natural_fraction_den_le

#print axioms accepted_certificate_point
end Reference.IV04ConcreteOracleSearchProof
