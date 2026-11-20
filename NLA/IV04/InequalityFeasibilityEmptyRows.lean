module

public import NLA.IV04.InequalityCertificateRawSoundness

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational Reference.IV04AffinePolyhedronSteps
open scoped Matrix
namespace IV04.Paper.InequalityFeasibilityNP
open IV04.Paper.InequalityCertificate

theorem empty_row_instance {n : ℕ} (A : Matrix (Fin 0) (Fin n) ℤ) (b : Fin 0 → ℤ) :
    integerMatrixInstanceCode A b=[] := by
  simp [integerMatrixInstanceCode,payloadListCode]

theorem empty_row_certificate :
    polynomialInequalitySystemVerifier (pair [] (inequalityIntegerCertificateCode [] 1))=[true] := by
  have h := (inequality_integer_system_verifier_exact [] [] 1).mpr (by simp)
  simpa [inequalityIntegerSystemCode,inequalityTypedSystemCode,inequalitySystemCode,
    payloadListCode,inequalityIntegerCertificateCode] using h

theorem arbitrary_certificate_matrix_sound_all_rows {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (certificate : List Bool)
    (haccept : polynomialInequalitySystemVerifier (pair (integerMatrixInstanceCode A b) certificate)=[true]) :
    ∃ x, feasible (integerRealMatrix A) (integerRealVector b) x := by
  by_cases hm : 0<m
  · exact arbitrary_certificate_sound A b hm certificate haccept
  · have hm0 : m=0 := by omega
    subst m
    exact ⟨0,fun i => Fin.elim0 i⟩

theorem real_feasible_iff_binary_certificate_all_rows {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    (∃ x, feasible (integerRealMatrix A) (integerRealVector b) x) ↔
    ∃ certificate : List Bool,
      certificate.length≤ inequalityInstanceLengthPolynomial (integerMatrixInstanceCode A b).length ∧
      polynomialInequalitySystemVerifier (pair (integerMatrixInstanceCode A b) certificate)=[true] := by
  by_cases hm : 0<m
  · exact real_feasible_iff_arbitrary_bounded_certificate A b hm
  · have hm0 : m=0 := by omega
    subst m
    constructor
    · intro _
      refine ⟨inequalityIntegerCertificateCode [] 1,?_,?_⟩
      · rw [empty_row_instance]
        norm_num [inequalityIntegerCertificateCode,payloadListCode,pair_length,
          inequalityInstanceLengthPolynomial]
      · rw [empty_row_instance]
        exact empty_row_certificate
    · rintro ⟨certificate,_,haccept⟩
      exact arbitrary_certificate_matrix_sound_all_rows A b certificate haccept

#print axioms empty_row_instance
#print axioms empty_row_certificate
#print axioms arbitrary_certificate_matrix_sound_all_rows
#print axioms real_feasible_iff_binary_certificate_all_rows
end IV04.Paper.InequalityFeasibilityNP
