module

public import NLA.IV04.InequalityFeasibilityNP

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational
namespace IV04.Paper.InequalityFeasibilityNP
open IV04.Paper.InequalityCertificate

def prefixFeasibilityLanguage : Language := {query | ∃ inputCode initialBits : List Bool,
  query=pair inputCode initialBits ∧ ∃ tail : List Bool,
    (initialBits++tail).length≤ inequalityInstanceLengthPolynomial inputCode.length ∧
    polynomialInequalitySystemVerifier (pair inputCode (initialBits++tail))=[true]}

def prefixInequalityVerifier (input : List Bool) : List Bool :=
  andBit (Cobham.eqFlag (pairFst input)
    (pair (pairFst (pairFst input)) (pairSnd (pairFst input))))
    (boundedInequalityVerifier (pair (pairFst (pairFst input))
      (pairSnd (pairFst input)++pairSnd input)))

def prefixInequalityVerifierLanguage : Language :=
  {input | prefixInequalityVerifier input=[true]}

theorem certificate_bound_monotone {N M : ℕ} (h : N≤M) :
    inequalityInstanceLengthPolynomial N≤ inequalityInstanceLengthPolynomial M := by
  unfold inequalityInstanceLengthPolynomial
  apply Nat.mul_le_mul
  · omega
  · have hs : N*N≤M*M := Nat.mul_le_mul h h
    nlinarith

theorem prefix_inequality_verifier_mem_fp : prefixInequalityVerifier ∈ FP := by
  have hfirst : (fun z => pairFst (pairFst z)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := pairFst) Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hprefix : (fun z => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := pairSnd) Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hquery := Cobham.pairFn_mem_FP hfirst hprefix
  have happend := Cobham.appendFn_mem_FP hprefix Cobham.sndBlock_mem_FP
  have hinput := Cobham.pairFn_mem_FP hfirst happend
  exact andBitFn_mem_FP (eqFlagFn_mem_FP Cobham.fstBlock_mem_FP hquery)
    (mem_FP_comp (g := boundedInequalityVerifier) hinput bounded_inequality_verifier_mem_fp)

theorem prefix_inequality_verifier_flag (input : List Bool) :
    prefixInequalityVerifier input=[true] ∨ prefixInequalityVerifier input=[false] :=
  andBit_flag _ _

theorem prefix_inequality_verifier_exact (query tail : List Bool) :
    prefixInequalityVerifier (pair query tail)=[true] ↔
      query=pair (pairFst query) (pairSnd query) ∧
      polynomialInequalitySystemVerifier (pair (pairFst query) (pairSnd query++tail))=[true] ∧
      (pairSnd query++tail).length≤ inequalityInstanceLengthPolynomial (pairFst query).length := by
  rw [prefixInequalityVerifier,Cobham.andBit_eq_true_iff
    (Cobham.eqFlag_flag _ _) (bounded_inequality_verifier_flag _),
    Cobham.eqFlag_eq_true_iff]
  simp only [pairFst_pair,pairSnd_pair,bounded_inequality_verifier_pair]

theorem prefix_inequality_verifier_language_mem_p : prefixInequalityVerifierLanguage ∈ P := by
  apply mem_P_of_decisionFn prefix_inequality_verifier_mem_fp
  intro input
  change prefixInequalityVerifier input=[true] ↔ _
  rcases prefix_inequality_verifier_flag input with h | h <;> simp [h]

theorem prefix_inequality_verifier_balanced (query tail : List Bool)
    (h : pair query tail ∈ prefixInequalityVerifierLanguage) :
    tail.length≤ certificateLengthPolynomial.eval query.length := by
  obtain ⟨hq,_,hlen⟩ := (prefix_inequality_verifier_exact query tail).mp h
  rw [certificate_polynomial_eval]
  have hsize := congrArg List.length hq
  rw [pair_length] at hsize
  have hi : (pairFst query).length≤query.length := by omega
  have hmono := certificate_bound_monotone hi
  rw [List.length_append] at hlen
  omega

theorem prefix_feasibility_iff_verifier (query : List Bool) :
    query ∈ prefixFeasibilityLanguage ↔
      ∃ tail : List Bool, pair query tail ∈ prefixInequalityVerifierLanguage := by
  constructor
  · rintro ⟨inputCode,initialBits,rfl,tail,hlen,haccept⟩
    refine ⟨tail,?_⟩
    change prefixInequalityVerifier (pair (pair inputCode initialBits) tail)=[true]
    apply (prefix_inequality_verifier_exact _ _).mpr
    simp only [pairFst_pair,pairSnd_pair]
    exact ⟨True.intro,haccept,hlen⟩
  · rintro ⟨tail,haccept⟩
    change prefixInequalityVerifier (pair query tail)=[true] at haccept
    obtain ⟨hq,hv,hlen⟩ := (prefix_inequality_verifier_exact _ _).mp haccept
    exact ⟨pairFst query,pairSnd query,hq,tail,hlen,hv⟩

theorem prefix_feasibility_language_mem_np : prefixFeasibilityLanguage ∈ NP := by
  exact mem_NP_of_poly_witness certificateLengthPolynomial
    prefix_inequality_verifier_language_mem_p prefix_inequality_verifier_balanced
    prefix_feasibility_iff_verifier

theorem prefix_query_exact (inputCode initialBits : List Bool) :
    pair inputCode initialBits ∈ prefixFeasibilityLanguage ↔
      ∃ tail : List Bool,
        (initialBits++tail).length≤ inequalityInstanceLengthPolynomial inputCode.length ∧
        polynomialInequalitySystemVerifier (pair inputCode (initialBits++tail))=[true] := by
  rw [prefix_feasibility_iff_verifier]
  apply exists_congr
  intro tail
  change prefixInequalityVerifier (pair (pair inputCode initialBits) tail)=[true] ↔ _
  rw [prefix_inequality_verifier_exact]
  simp only [pairFst_pair,pairSnd_pair,true_and]
  exact and_comm

theorem prefix_empty_iff_integer_feasibility (inputCode : List Bool) :
    pair inputCode [] ∈ prefixFeasibilityLanguage ↔ inputCode ∈ integerFeasibilityLanguage := by
  rw [prefix_query_exact,integer_feasibility_iff_bounded_binary_certificate]
  simp only [List.nil_append]

#print axioms certificate_bound_monotone
#print axioms prefix_inequality_verifier_mem_fp
#print axioms prefix_inequality_verifier_exact
#print axioms prefix_inequality_verifier_language_mem_p
#print axioms prefix_inequality_verifier_balanced
#print axioms prefix_feasibility_iff_verifier
#print axioms prefix_feasibility_language_mem_np
#print axioms prefix_query_exact
#print axioms prefix_empty_iff_integer_feasibility
end IV04.Paper.InequalityFeasibilityNP
