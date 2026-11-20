module

public import NLA.IV04.InequalityCertificateRawSoundness

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational Reference.IV04AffinePolyhedronSteps
open scoped Matrix
namespace IV04.Paper.InequalityFeasibilityNP
open IV04.Paper.InequalityCertificate

def wordMatrixRowCode {m n : ℕ} (A : Matrix (Fin m) (Fin n) (List Bool))
    (b : Fin m → List Bool) (i : Fin m) : List Bool :=
  pair (payloadListCode (List.ofFn (A i))) (b i)

def wordMatrixInstanceCode {m n : ℕ} (A : Matrix (Fin m) (Fin n) (List Bool))
    (b : Fin m → List Bool) : List Bool := payloadListCode (List.ofFn (wordMatrixRowCode A b))

def wordMatrixValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) (List Bool)) :
    Matrix (Fin m) (Fin n) ℤ := fun i j => signedWordValue (A i j)

def wordVectorValue {m : ℕ} (b : Fin m → List Bool) : Fin m → ℤ :=
  fun i => signedWordValue (b i)

def integerFeasibilityLanguage : Language := {inputCode | ∃ m n : ℕ,
  ∃ A : Matrix (Fin m) (Fin n) (List Bool), ∃ b : Fin m → List Bool,
    inputCode=wordMatrixInstanceCode A b ∧
    ∃ x, feasible (integerRealMatrix (wordMatrixValue A)) (integerRealVector (wordVectorValue b)) x}

theorem signed_dot_ofFn {n : ℕ} (a p : Fin n → List Bool) :
    signedPayloadDot (List.ofFn a) (List.ofFn p)=
      ∑ j, signedWordValue (a j)*signedWordValue (p j) := by
  rw [signed_dot_as_integer_dot,List.map_ofFn,List.map_ofFn,integer_dot_ofFn]
  rfl

theorem word_matrix_verifier_exact {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (List Bool)) (b : Fin m → List Bool)
    (numerators : Fin n → List Bool) (denominator : List Bool) :
    polynomialInequalitySystemVerifier (pair (wordMatrixInstanceCode A b)
      (pair (payloadListCode (List.ofFn numerators)) denominator))=[true] ↔
      0<wordValue denominator ∧
      feasible (integerRealMatrix (wordMatrixValue A)) (integerRealVector (wordVectorValue b))
        (fun j => (signedWordValue (numerators j) : ℝ)/(wordValue denominator : ℝ)) := by
  change polynomialInequalitySystemVerifier (inequalitySystemCode
    (List.ofFn (wordMatrixRowCode A b)) (List.ofFn numerators) denominator)=[true] ↔ _
  rw [inequality_system_verifier_code]
  constructor
  · rintro ⟨hd,hrows⟩
    refine ⟨hd,(matrix_fraction_feasible_iff _ _ _ _ hd).mpr ?_⟩
    intro i
    have hrow := hrows _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
    have h := (decoded_inequality_row_code (List.ofFn (A i))
      (List.ofFn numerators) (b i) denominator).mp hrow
    simpa only [signed_dot_ofFn,wordMatrixValue,wordVectorValue] using h.2
  · rintro ⟨hd,hfeasible⟩
    refine ⟨hd,?_⟩
    intro row hrow
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
    apply (decoded_inequality_row_code _ _ _ _).mpr
    refine ⟨by simp,?_⟩
    rw [signed_dot_ofFn]
    exact (matrix_fraction_feasible_iff _ _ _ _ hd).mp hfeasible i

theorem word_matrix_integer_certificate_exact {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (List Bool)) (b : Fin m → List Bool)
    (p : Fin n → ℤ) (d : ℕ) :
    polynomialInequalitySystemVerifier (pair (wordMatrixInstanceCode A b)
      (inequalityIntegerCertificateCode (integerVectorList p) d))=[true] ↔
      0<d ∧ feasible (integerRealMatrix (wordMatrixValue A)) (integerRealVector (wordVectorValue b))
        (fun j => (p j : ℝ)/(d : ℝ)) := by
  have hd : wordValue d.bits=d := by rw [word_value_foldr];exact IV04.Paper.bits_foldr d
  unfold inequalityIntegerCertificateCode integerVectorList
  rw [List.map_ofFn,word_matrix_verifier_exact,hd]
  simp only [Function.comp_apply,inequality_integer_word_value]

theorem decoded_row_fin_representation (numerators : List (List Bool))
    (denominator row : List Bool) (hrow : decodedInequalityRow numerators denominator row) :
    ∃ a : Fin numerators.length → List Bool, ∃ b : List Bool,
      row=pair (payloadListCode (List.ofFn a)) b ∧
      (∑ j, signedWordValue (a j)*signedWordValue (numerators.get j))≤
        signedWordValue b*(wordValue denominator : ℤ) := by
  obtain ⟨coefficients,bound,hcode,hlen,hdot⟩ := hrow
  let a : Fin numerators.length → List Bool :=
    fun j => coefficients.get (Fin.cast hlen.symm j)
  have ha : List.ofFn a=coefficients := by
    apply List.ext_get (by simp only [List.length_ofFn];exact hlen.symm)
    intro j hj₁ hj₂
    simp [a]
  refine ⟨a,bound,?_,?_⟩
  · simpa only [ha] using hcode
  · have h := signed_dot_ofFn a numerators.get
    rw [ha,List.ofFn_get] at h
    rwa [← h]

theorem raw_verifier_acceptance_has_feasible_matrix (inputCode certificate : List Bool)
    (haccept : polynomialInequalitySystemVerifier (pair inputCode certificate)=[true]) :
    inputCode ∈ integerFeasibilityLanguage := by
  classical
  obtain ⟨rows,numerators,denominator,hcode,hd,hrows⟩ :=
    (inequality_system_verifier_exact _).mp haccept
  have hinst := congrArg pairFst hcode
  simp only [inequalitySystemCode,pairFst_pair] at hinst
  have hrep (i : Fin rows.length) : ∃ a : Fin numerators.length → List Bool,
      ∃ b : List Bool, rows.get i=pair (payloadListCode (List.ofFn a)) b ∧
      (∑ j, signedWordValue (a j)*signedWordValue (numerators.get j))≤
        signedWordValue b*(wordValue denominator : ℤ) :=
    decoded_row_fin_representation numerators denominator (rows.get i)
      (hrows _ (List.get_mem _ _))
  choose A b he hineq using hrep
  refine ⟨rows.length,numerators.length,A,b,?_,?_⟩
  · change inputCode=payloadListCode (List.ofFn (wordMatrixRowCode A b))
    have hr : List.ofFn (wordMatrixRowCode A b)=rows := by
      calc
        List.ofFn (wordMatrixRowCode A b)=List.ofFn rows.get := by
          apply congrArg List.ofFn
          funext i
          exact (he i).symm
        _=rows := List.ofFn_get rows
    rw [hr]
    exact hinst
  · refine ⟨fun j => (signedWordValue (numerators.get j) : ℝ)/(wordValue denominator : ℝ),?_⟩
    exact (matrix_fraction_feasible_iff _ _ _ _ hd).mpr hineq

#print axioms signed_dot_ofFn
#print axioms word_matrix_verifier_exact
#print axioms word_matrix_integer_certificate_exact
#print axioms decoded_row_fin_representation
#print axioms raw_verifier_acceptance_has_feasible_matrix
end IV04.Paper.InequalityFeasibilityNP
