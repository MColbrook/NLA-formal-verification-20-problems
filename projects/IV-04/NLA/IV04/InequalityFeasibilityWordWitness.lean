module

public import NLA.IV04.InequalityFeasibilityWordSemantics
public import NLA.IV04.InequalityFeasibilityEmptyRows

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational Reference.IV04AffinePolyhedronSteps
open scoped Matrix
namespace IV04.Paper.InequalityFeasibilityNP
open IV04.Paper.InequalityCertificate

theorem signed_word_magnitude_le_pow_length (word : List Bool) :
    |signedWordValue word|≤((2^word.length : ℕ) : ℤ) := by
  have hv := word_value_lt_pow_length word.tail
  have hlen : word.tail.length≤word.length := by simp
  have hpow : (2 : ℕ)^word.tail.length≤2^word.length := Nat.pow_le_pow_right (by omega) hlen
  have hn : (signedWordValue word).natAbs≤2^word.length := by
    rw [signed_word_abs_value]
    omega
  have hc : ((signedWordValue word).natAbs : ℤ)≤((2^word.length : ℕ) : ℤ) := by exact_mod_cast hn
  simpa only [Int.natCast_natAbs] using hc

theorem word_matrix_row_length_le_instance {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (List Bool)) (b : Fin m → List Bool) (i : Fin m) :
    (wordMatrixRowCode A b i).length≤(wordMatrixInstanceCode A b).length :=
  payload_member_length_le _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem word_matrix_dimensions_le_instance {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (List Bool)) (b : Fin m → List Bool) (hm : 0<m) :
    m≤(wordMatrixInstanceCode A b).length ∧ n≤(wordMatrixInstanceCode A b).length := by
  constructor
  · simpa only [List.length_ofFn,wordMatrixInstanceCode] using
      payload_count_le_code_length (List.ofFn (wordMatrixRowCode A b))
  · let i : Fin m := ⟨0,hm⟩
    have hrow := word_matrix_row_length_le_instance A b i
    have hcount := payload_count_le_code_length (List.ofFn (A i))
    simp only [List.length_ofFn] at hcount
    rw [wordMatrixRowCode,pair_length] at hrow
    omega

theorem word_matrix_coefficients_le_instance_power {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (List Bool)) (b : Fin m → List Bool) :
    (∀ i j, |wordMatrixValue A i j|≤((2^(wordMatrixInstanceCode A b).length : ℕ) : ℤ)) ∧
    (∀ i, |wordVectorValue b i|≤((2^(wordMatrixInstanceCode A b).length : ℕ) : ℤ)) := by
  constructor
  · intro i j
    have hw := payload_member_length_le _ _ (List.mem_ofFn.mpr ⟨j,rfl⟩ : A i j ∈ List.ofFn (A i))
    have hr := word_matrix_row_length_le_instance A b i
    rw [wordMatrixRowCode,pair_length] at hr
    have hlen : (A i j).length≤(wordMatrixInstanceCode A b).length := by omega
    exact (signed_word_magnitude_le_pow_length _).trans (by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤(2 : ℕ)) hlen)
  · intro i
    have hr := word_matrix_row_length_le_instance A b i
    rw [wordMatrixRowCode,pair_length] at hr
    have hlen : (b i).length≤(wordMatrixInstanceCode A b).length := by omega
    exact (signed_word_magnitude_le_pow_length _).trans (by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤(2 : ℕ)) hlen)

theorem word_matrix_witness_bound_le_instance_polynomial {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (List Bool)) (b : Fin m → List Bool) (hm : 0<m) :
    inequalityWitnessLengthBound m n (wordMatrixInstanceCode A b).length≤
      inequalityInstanceLengthPolynomial (wordMatrixInstanceCode A b).length := by
  obtain ⟨hmN,hnN⟩ := word_matrix_dimensions_le_instance A b hm
  let N := (wordMatrixInstanceCode A b).length
  change m≤N at hmN
  change n≤N at hnN
  have hsquare : n*n≤N*N := Nat.mul_le_mul hnN hnN
  have hbase : m+n+2*N≤4*N := by omega
  have hprod : n*(m+n+2*N)≤N*(4*N) := Nat.mul_le_mul hnN hbase
  have hK : inequalityWitnessExponent m n N≤5*N*N := by
    unfold inequalityWitnessExponent
    nlinarith
  unfold inequalityWitnessLengthBound inequalityInstanceLengthPolynomial
  change (4*n+1)*(inequalityWitnessExponent m n N+3)≤(4*N+1)*(5*N*N+3)
  exact Nat.mul_le_mul (by omega) (by omega)

theorem feasible_word_matrix_has_polynomial_binary_certificate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (List Bool)) (b : Fin m → List Bool)
    (hne : ∃ x, feasible (integerRealMatrix (wordMatrixValue A)) (integerRealVector (wordVectorValue b)) x) :
    ∃ certificate : List Bool,
      certificate.length≤ inequalityInstanceLengthPolynomial (wordMatrixInstanceCode A b).length ∧
      polynomialInequalitySystemVerifier (pair (wordMatrixInstanceCode A b) certificate)=[true] := by
  by_cases hm : 0<m
  · obtain ⟨hA,hb⟩ := word_matrix_coefficients_le_instance_power A b
    obtain ⟨p,d,hd,_,_,hlen,haccept⟩ := exists_polynomial_encoded_feasible_certificate
      (wordMatrixValue A) (wordVectorValue b) (wordMatrixInstanceCode A b).length hA hb hne
    refine ⟨inequalityIntegerCertificateCode (integerVectorList p) d,
      hlen.trans (word_matrix_witness_bound_le_instance_polynomial A b hm),?_⟩
    apply (word_matrix_integer_certificate_exact A b p d).mpr
    exact (integer_matrix_verifier_exact _ _ p d).mp haccept
  · have hm0 : m=0 := by omega
    subst m
    refine ⟨inequalityIntegerCertificateCode [] 1,?_,?_⟩
    · simp [wordMatrixInstanceCode,inequalityIntegerCertificateCode,
        inequalityInstanceLengthPolynomial,payloadListCode,pair_length]
    · have hi : wordMatrixInstanceCode A b=[] := by simp [wordMatrixInstanceCode,payloadListCode]
      rw [hi]
      exact empty_row_certificate

theorem integer_feasibility_iff_bounded_binary_certificate (inputCode : List Bool) :
    inputCode ∈ integerFeasibilityLanguage ↔
      ∃ certificate : List Bool,
        certificate.length≤ inequalityInstanceLengthPolynomial inputCode.length ∧
        polynomialInequalitySystemVerifier (pair inputCode certificate)=[true] := by
  constructor
  · rintro ⟨m,n,A,b,rfl,hne⟩
    exact feasible_word_matrix_has_polynomial_binary_certificate A b hne
  · rintro ⟨certificate,_,haccept⟩
    exact raw_verifier_acceptance_has_feasible_matrix inputCode certificate haccept

#print axioms signed_word_magnitude_le_pow_length
#print axioms word_matrix_row_length_le_instance
#print axioms word_matrix_dimensions_le_instance
#print axioms word_matrix_coefficients_le_instance_power
#print axioms word_matrix_witness_bound_le_instance_polynomial
#print axioms feasible_word_matrix_has_polynomial_binary_certificate
#print axioms integer_feasibility_iff_bounded_binary_certificate
end IV04.Paper.InequalityFeasibilityNP
