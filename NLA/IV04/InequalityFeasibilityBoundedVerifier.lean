module

public import NLA.IV04.InequalityFeasibilityEmptyRows
public import NLA.IV04.Complexitylib.Classes.P.Unary
public import NLA.IV04.Complexitylib.Classes.P.DecisionFn
public import NLA.IV04.Complexitylib.Classes.NP.Verifier

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational
namespace IV04.Paper.InequalityFeasibilityNP
open IV04.Paper.InequalityCertificate

noncomputable def certificateLengthPolynomial : Polynomial ℕ :=
  (Polynomial.C 4*Polynomial.X+Polynomial.C 1)*
    (Polynomial.C 5*Polynomial.X*Polynomial.X+Polynomial.C 3)

theorem certificate_polynomial_eval (N : ℕ) :
    certificateLengthPolynomial.eval N=inequalityInstanceLengthPolynomial N := by
  simp [certificateLengthPolynomial,inequalityInstanceLengthPolynomial]

def certificateRuler (inputCode : List Bool) : List Bool :=
  List.replicate (inequalityInstanceLengthPolynomial inputCode.length) true

def boundedInequalityVerifier (input : List Bool) : List Bool :=
  andBit (polynomialInequalitySystemVerifier input)
    (Cobham.lenLeFlag (certificateRuler (pairFst input)) (pairSnd input))

def boundedInequalityVerifierLanguage : Language :=
  {input | boundedInequalityVerifier input=[true]}

theorem certificate_ruler_mem_fp : certificateRuler ∈ FP := by
  have hn : UnaryFn fun z : List Bool => z.length := UnaryFn.length id_mem_FP
  exact (((UnaryFn.const 4).mul hn).add (UnaryFn.const 1)).mul
    ((((UnaryFn.const 5).mul hn).mul hn).add (UnaryFn.const 3))

theorem bounded_inequality_verifier_mem_fp : boundedInequalityVerifier ∈ FP := by
  exact andBitFn_mem_FP inequality_system_verifier_mem_fp
    (lenLeFlagFn_mem_FP
      (mem_FP_comp (f := pairFst) (g := certificateRuler) Cobham.fstBlock_mem_FP certificate_ruler_mem_fp)
      Cobham.sndBlock_mem_FP)

theorem bounded_inequality_verifier_flag (input : List Bool) :
    boundedInequalityVerifier input=[true] ∨ boundedInequalityVerifier input=[false] :=
  andBit_flag _ _

theorem bounded_inequality_verifier_exact (input : List Bool) :
    boundedInequalityVerifier input=[true] ↔
      polynomialInequalitySystemVerifier input=[true] ∧
      (pairSnd input).length≤ inequalityInstanceLengthPolynomial (pairFst input).length := by
  rw [boundedInequalityVerifier,Cobham.andBit_eq_true_iff
    (inequality_system_verifier_flag _) (Cobham.lenLeFlag_flag _ _),
    Cobham.lenLeFlag_eq_true_iff]
  simp only [certificateRuler,List.length_replicate]

theorem bounded_inequality_verifier_pair (inputCode certificate : List Bool) :
    boundedInequalityVerifier (pair inputCode certificate)=[true] ↔
      polynomialInequalitySystemVerifier (pair inputCode certificate)=[true] ∧
      certificate.length≤ inequalityInstanceLengthPolynomial inputCode.length := by
  rw [bounded_inequality_verifier_exact]
  simp only [pairFst_pair,pairSnd_pair]

theorem bounded_inequality_verifier_language_mem_p : boundedInequalityVerifierLanguage ∈ P := by
  apply mem_P_of_decisionFn bounded_inequality_verifier_mem_fp
  intro input
  change boundedInequalityVerifier input=[true] ↔ _
  rcases bounded_inequality_verifier_flag input with h | h <;> simp [h]

theorem bounded_inequality_verifier_balanced (inputCode certificate : List Bool)
    (h : pair inputCode certificate ∈ boundedInequalityVerifierLanguage) :
    certificate.length≤ certificateLengthPolynomial.eval inputCode.length := by
  rw [certificate_polynomial_eval]
  exact ((bounded_inequality_verifier_pair _ _).mp h).2

#print axioms certificate_polynomial_eval
#print axioms certificate_ruler_mem_fp
#print axioms bounded_inequality_verifier_mem_fp
#print axioms bounded_inequality_verifier_flag
#print axioms bounded_inequality_verifier_exact
#print axioms bounded_inequality_verifier_pair
#print axioms bounded_inequality_verifier_language_mem_p
#print axioms bounded_inequality_verifier_balanced
end IV04.Paper.InequalityFeasibilityNP
