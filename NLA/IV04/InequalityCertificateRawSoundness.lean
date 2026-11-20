module

public import NLA.IV04.InequalityCertificateInstanceLength

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational Reference.IV04AffinePolyhedronSteps
open scoped Matrix
namespace IV04.Paper.InequalityCertificate

theorem payload_code_injective : Function.Injective payloadListCode := by
  intro left
  induction left with
  | nil =>
    intro right h
    cases right with
    | nil => rfl
    | cons word rest =>
      have hl := congrArg List.length h
      simp only [payloadListCode,pair_length,List.length_nil] at hl
      omega
  | cons word rest ih =>
    intro right h
    cases right with
    | nil =>
      have hl := congrArg List.length h
      simp only [payloadListCode,pair_length,List.length_nil] at hl
      omega
    | cons other tail =>
      have hf := congrArg pairFst h
      have hs := congrArg pairSnd h
      simp only [payloadListCode,pairFst_pair] at hf
      simp only [payloadListCode,pairSnd_pair] at hs
      exact congrArg₂ List.cons hf (ih hs)

theorem signed_dot_as_integer_dot (left right : List (List Bool)) :
    signedPayloadDot left right=
      inequalityIntegerDot (left.map signedWordValue) (right.map signedWordValue) := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a rest ih =>
    cases right with
    | nil => rfl
    | cons p tail => simp only [signedPayloadDot,List.map_cons,inequalityIntegerDot,ih]

theorem decoded_matrix_row_sound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (i : Fin m)
    (numerators : List (List Bool)) (denominator : List Bool)
    (hrow : decodedInequalityRow numerators denominator (integerMatrixRowCode A b i)) :
    n=numerators.length ∧
      inequalityIntegerDot (List.ofFn (A i)) (numerators.map signedWordValue)≤
        b i*(wordValue denominator : ℤ) := by
  obtain ⟨coefficients,bound,hcode,hlen,hdot⟩ := hrow
  have hc := congrArg pairFst hcode
  have hb := congrArg pairSnd hcode
  simp only [integerMatrixRowCode,pairFst_pair] at hc
  simp only [integerMatrixRowCode,pairSnd_pair] at hb
  have hcoeff := (payload_code_injective hc).symm
  subst coefficients
  subst bound
  constructor
  · simpa only [List.length_map,List.length_ofFn] using hlen
  · simpa [signed_dot_as_integer_dot,List.map_map,Function.comp_def,inequality_integer_word_value] using hdot

theorem arbitrary_certificate_sound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m)
    (certificate : List Bool)
    (haccept : polynomialInequalitySystemVerifier (pair (integerMatrixInstanceCode A b) certificate)=[true]) :
    ∃ x, feasible (integerRealMatrix A) (integerRealVector b) x := by
  obtain ⟨rows,numerators,denominator,hcode,hd,hrows⟩ :=
    (inequality_system_verifier_exact _).mp haccept
  have hinst := congrArg pairFst hcode
  simp only [inequalitySystemCode,pairFst_pair] at hinst
  have hdecoded : List.ofFn (integerMatrixRowCode A b)=rows := payload_code_injective hinst
  have hrow (i : Fin m) : decodedInequalityRow numerators denominator (integerMatrixRowCode A b i) := by
    apply hrows
    rw [← hdecoded]
    exact List.mem_ofFn.mpr ⟨i,rfl⟩
  have hmatrix (i : Fin m) := decoded_matrix_row_sound A b i numerators denominator (hrow i)
  have hlen : numerators.length=n := (hmatrix ⟨0,hm⟩).1.symm
  cases hlen
  let p : Fin numerators.length → ℤ := fun j => signedWordValue (numerators.get j)
  have hp : List.ofFn p=numerators.map signedWordValue := by
    change List.ofFn (signedWordValue ∘ numerators.get)=numerators.map signedWordValue
    rw [← List.map_ofFn,List.ofFn_get]
  refine ⟨fun j => (p j : ℝ)/(wordValue denominator : ℝ),?_⟩
  apply (matrix_fraction_feasible_iff A b p (wordValue denominator) hd).mpr
  intro i
  have hi := (hmatrix i).2
  rw [← hp,integer_dot_ofFn] at hi
  exact hi

theorem real_feasible_iff_arbitrary_bounded_certificate {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) :
    (∃ x, feasible (integerRealMatrix A) (integerRealVector b) x) ↔
    ∃ certificate : List Bool,
      certificate.length≤ inequalityInstanceLengthPolynomial (integerMatrixInstanceCode A b).length ∧
      polynomialInequalitySystemVerifier (pair (integerMatrixInstanceCode A b) certificate)=[true] := by
  constructor
  · intro hne
    obtain ⟨p,d,hlen,haccept⟩ := (real_feasible_iff_certificate_polynomial_in_actual_instance A b hm).mp hne
    exact ⟨inequalityIntegerCertificateCode (integerVectorList p) d,hlen,haccept⟩
  · rintro ⟨certificate,_,haccept⟩
    exact arbitrary_certificate_sound A b hm certificate haccept

theorem actual_fp_verifier_and_binary_polynomial_certificates {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (hm : 0<m) :
    polynomialInequalitySystemVerifier ∈ FP ∧
    ((∃ x, feasible (integerRealMatrix A) (integerRealVector b) x) ↔
      ∃ certificate : List Bool,
        certificate.length≤ inequalityInstanceLengthPolynomial (integerMatrixInstanceCode A b).length ∧
        polynomialInequalitySystemVerifier (pair (integerMatrixInstanceCode A b) certificate)=[true]) := by
  exact ⟨inequality_system_verifier_mem_fp,real_feasible_iff_arbitrary_bounded_certificate A b hm⟩

#print axioms payload_code_injective
#print axioms signed_dot_as_integer_dot
#print axioms decoded_matrix_row_sound
#print axioms arbitrary_certificate_sound
#print axioms real_feasible_iff_arbitrary_bounded_certificate
#print axioms actual_fp_verifier_and_binary_polynomial_certificates
end IV04.Paper.InequalityCertificate
