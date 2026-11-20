module

public import NLA.IV04.InequalityCertificateFeasibleWitness

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational Reference.IV04AffinePolyhedronSteps
open scoped Matrix
namespace IV04.Paper.InequalityCertificate

def integerMatrixRowCode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (i : Fin m) : List Bool :=
  pair (payloadListCode ((List.ofFn (A i)).map inequalityIntegerWord)) (inequalityIntegerWord (b i))

def integerMatrixInstanceCode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) : List Bool := payloadListCode (List.ofFn (integerMatrixRowCode A b))

def inequalityInstanceLengthPolynomial (N : ℕ) : ℕ := (4*N+1)*(5*N*N+3)

theorem payload_member_length_le (words : List (List Bool)) (word : List Bool)
    (hw : word ∈ words) : word.length≤(payloadListCode words).length := by
  induction words with
  | nil => simp at hw
  | cons first rest ih =>
    simp only [List.mem_cons] at hw
    rw [payloadListCode,pair_length]
    rcases hw with h | h
    · subst word; omega
    · have hi := ih h; omega

theorem payload_count_le_code_length (words : List (List Bool)) :
    words.length≤(payloadListCode words).length := by
  rw [inequality_payload_list_code_length]
  omega

theorem matrix_row_length_le_instance {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (i : Fin m) :
    (integerMatrixRowCode A b i).length≤(integerMatrixInstanceCode A b).length := by
  exact payload_member_length_le _ _ (List.mem_ofFn.mpr ⟨i,rfl⟩)

theorem integer_matrix_code_framing {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (p : Fin n → ℤ) (d : ℕ) :
    inequalityIntegerSystemCode (integerMatrixRows A b) (integerVectorList p) d=
      pair (integerMatrixInstanceCode A b)
        (inequalityIntegerCertificateCode (integerVectorList p) d) := by
  simp [inequalityIntegerSystemCode,inequalityTypedSystemCode,inequalitySystemCode,
    integerMatrixRows,integerMatrixInstanceCode,inequalityIntegerCertificateCode]
  rfl

theorem matrix_dimensions_le_instance_length {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) :
    m≤(integerMatrixInstanceCode A b).length ∧ n≤(integerMatrixInstanceCode A b).length := by
  constructor
  · simpa only [List.length_ofFn,integerMatrixInstanceCode] using payload_count_le_code_length (List.ofFn (integerMatrixRowCode A b))
  · let i : Fin m := ⟨0,hm⟩
    have hrow := matrix_row_length_le_instance A b i
    have hcount := payload_count_le_code_length ((List.ofFn (A i)).map inequalityIntegerWord)
    simp only [List.length_map,List.length_ofFn] at hcount
    rw [integerMatrixRowCode,pair_length] at hrow
    omega

theorem integer_word_magnitude_le_pow_length (z : ℤ) :
    |z|≤((2^(inequalityIntegerWord z).length : ℕ) : ℤ) := by
  have hn : z.natAbs≤2^(inequalityIntegerWord z).length := by
    have hsize := Nat.lt_size_self z.natAbs
    rw [inequality_integer_word_length]
    have hpow : (2 : ℕ)^z.natAbs.size≤2^(z.natAbs.size+1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hcast : (z.natAbs : ℤ)≤((2^(inequalityIntegerWord z).length : ℕ) : ℤ) := by exact_mod_cast hn
  simpa only [Int.natCast_natAbs] using hcast

theorem matrix_coefficients_le_instance_power {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    (∀ i j, |A i j|≤((2^(integerMatrixInstanceCode A b).length : ℕ) : ℤ)) ∧
    (∀ i, |b i|≤((2^(integerMatrixInstanceCode A b).length : ℕ) : ℤ)) := by
  constructor
  · intro i j
    have hm : inequalityIntegerWord (A i j) ∈ (List.ofFn (A i)).map inequalityIntegerWord := by
      exact List.mem_map.mpr ⟨A i j,List.mem_ofFn.mpr ⟨j,rfl⟩,rfl⟩
    have hw := payload_member_length_le _ _ hm
    have hr := matrix_row_length_le_instance A b i
    rw [integerMatrixRowCode,pair_length] at hr
    have hlen : (inequalityIntegerWord (A i j)).length≤(integerMatrixInstanceCode A b).length := by omega
    exact (integer_word_magnitude_le_pow_length _).trans (by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤(2 : ℕ)) hlen)
  · intro i
    have hr := matrix_row_length_le_instance A b i
    rw [integerMatrixRowCode,pair_length] at hr
    have hlen : (inequalityIntegerWord (b i)).length≤(integerMatrixInstanceCode A b).length := by omega
    exact (integer_word_magnitude_le_pow_length _).trans (by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 1≤(2 : ℕ)) hlen)

theorem witness_bound_le_instance_polynomial {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) :
    inequalityWitnessLengthBound m n (integerMatrixInstanceCode A b).length≤
      inequalityInstanceLengthPolynomial (integerMatrixInstanceCode A b).length := by
  obtain ⟨hmN,hnN⟩ := matrix_dimensions_le_instance_length A b hm
  let N := (integerMatrixInstanceCode A b).length
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

theorem real_feasible_iff_certificate_polynomial_in_actual_instance {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) :
    (∃ x, feasible (integerRealMatrix A) (integerRealVector b) x) ↔
    ∃ p : Fin n → ℤ, ∃ d : ℕ,
      (inequalityIntegerCertificateCode (integerVectorList p) d).length≤
        inequalityInstanceLengthPolynomial (integerMatrixInstanceCode A b).length ∧
      polynomialInequalitySystemVerifier
        (pair (integerMatrixInstanceCode A b)
          (inequalityIntegerCertificateCode (integerVectorList p) d))=[true] := by
  obtain ⟨hA,hb⟩ := matrix_coefficients_le_instance_power A b
  constructor
  · intro hne
    obtain ⟨p,d,hlen,haccept⟩ := (feasible_iff_bounded_verifier_certificate A b
      (integerMatrixInstanceCode A b).length hA hb).mp hne
    refine ⟨p,d,hlen.trans (witness_bound_le_instance_polynomial A b hm),?_⟩
    rwa [integer_matrix_code_framing] at haccept
  · rintro ⟨p,d,_,haccept⟩
    rw [← integer_matrix_code_framing] at haccept
    exact ⟨_,((integer_matrix_verifier_exact A b p d).mp haccept).2⟩

#print axioms payload_member_length_le
#print axioms payload_count_le_code_length
#print axioms matrix_row_length_le_instance
#print axioms integer_matrix_code_framing
#print axioms matrix_dimensions_le_instance_length
#print axioms integer_word_magnitude_le_pow_length
#print axioms matrix_coefficients_le_instance_power
#print axioms witness_bound_le_instance_polynomial
#print axioms real_feasible_iff_certificate_polynomial_in_actual_instance
end IV04.Paper.InequalityCertificate
