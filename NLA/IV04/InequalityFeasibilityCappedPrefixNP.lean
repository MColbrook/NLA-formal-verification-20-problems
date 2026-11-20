module

public import NLA.IV04.InequalityFeasibilityPrefixNP

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational
namespace IV04.Paper.InequalityFeasibilityNP
open IV04.Paper.InequalityCertificate

def cappedPrefixFeasibilityLanguage : Language := {query | ∃ inputCode ruler initialBits : List Bool,
  query=pair inputCode (pair ruler initialBits) ∧ ∃ tail : List Bool,
    (initialBits++tail).length≤ruler.length ∧
    (initialBits++tail).length≤ inequalityInstanceLengthPolynomial inputCode.length ∧
    polynomialInequalitySystemVerifier (pair inputCode (initialBits++tail))=[true]}

def cappedPrefixInequalityVerifier (input : List Bool) : List Bool :=
  andBit (Cobham.eqFlag (pairFst input)
    (pair (pairFst (pairFst input))
      (pair (pairFst (pairSnd (pairFst input))) (pairSnd (pairSnd (pairFst input))))))
    (andBit (Cobham.lenLeFlag (pairFst (pairSnd (pairFst input)))
      (pairSnd (pairSnd (pairFst input))++pairSnd input))
      (boundedInequalityVerifier (pair (pairFst (pairFst input))
        (pairSnd (pairSnd (pairFst input))++pairSnd input))))

def cappedPrefixInequalityVerifierLanguage : Language :=
  {input | cappedPrefixInequalityVerifier input=[true]}

theorem capped_prefix_inequality_verifier_mem_fp : cappedPrefixInequalityVerifier ∈ FP := by
  have hfirst : (fun z => pairFst (pairFst z)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := pairFst) Cobham.fstBlock_mem_FP Cobham.fstBlock_mem_FP
  have hpayload : (fun z => pairSnd (pairFst z)) ∈ FP :=
    mem_FP_comp (f := pairFst) (g := pairSnd) Cobham.fstBlock_mem_FP Cobham.sndBlock_mem_FP
  have hruler : (fun z => pairFst (pairSnd (pairFst z))) ∈ FP :=
    mem_FP_comp (g := pairFst) hpayload Cobham.fstBlock_mem_FP
  have hprefix : (fun z => pairSnd (pairSnd (pairFst z))) ∈ FP :=
    mem_FP_comp (g := pairSnd) hpayload Cobham.sndBlock_mem_FP
  have hquery := Cobham.pairFn_mem_FP hfirst (Cobham.pairFn_mem_FP hruler hprefix)
  have happend := Cobham.appendFn_mem_FP hprefix Cobham.sndBlock_mem_FP
  have hinput := Cobham.pairFn_mem_FP hfirst happend
  exact andBitFn_mem_FP (eqFlagFn_mem_FP Cobham.fstBlock_mem_FP hquery)
    (andBitFn_mem_FP (lenLeFlagFn_mem_FP hruler happend)
      (mem_FP_comp (g := boundedInequalityVerifier) hinput bounded_inequality_verifier_mem_fp))

theorem capped_prefix_inequality_verifier_flag (input : List Bool) :
    cappedPrefixInequalityVerifier input=[true] ∨ cappedPrefixInequalityVerifier input=[false] :=
  andBit_flag _ _

theorem capped_prefix_inequality_verifier_exact (query tail : List Bool) :
    cappedPrefixInequalityVerifier (pair query tail)=[true] ↔
      query=pair (pairFst query) (pair (pairFst (pairSnd query)) (pairSnd (pairSnd query))) ∧
      (pairSnd (pairSnd query)++tail).length≤(pairFst (pairSnd query)).length ∧
      polynomialInequalitySystemVerifier
        (pair (pairFst query) (pairSnd (pairSnd query)++tail))=[true] ∧
      (pairSnd (pairSnd query)++tail).length≤ inequalityInstanceLengthPolynomial (pairFst query).length := by
  rw [cappedPrefixInequalityVerifier,Cobham.andBit_eq_true_iff
    (Cobham.eqFlag_flag _ _) (andBit_flag _ _),
    Cobham.andBit_eq_true_iff (Cobham.lenLeFlag_flag _ _) (bounded_inequality_verifier_flag _),
    Cobham.eqFlag_eq_true_iff,Cobham.lenLeFlag_eq_true_iff]
  simp only [pairFst_pair,pairSnd_pair,bounded_inequality_verifier_pair]

theorem capped_prefix_inequality_verifier_language_mem_p : cappedPrefixInequalityVerifierLanguage ∈ P := by
  apply mem_P_of_decisionFn capped_prefix_inequality_verifier_mem_fp
  intro input
  change cappedPrefixInequalityVerifier input=[true] ↔ _
  rcases capped_prefix_inequality_verifier_flag input with h | h <;> simp [h]

theorem capped_prefix_inequality_verifier_balanced (query tail : List Bool)
    (h : pair query tail ∈ cappedPrefixInequalityVerifierLanguage) :
    tail.length≤ certificateLengthPolynomial.eval query.length := by
  obtain ⟨hq,_,_,hlen⟩ := (capped_prefix_inequality_verifier_exact query tail).mp h
  rw [certificate_polynomial_eval]
  have hsize := congrArg List.length hq
  rw [pair_length] at hsize
  have hi : (pairFst query).length≤query.length := by omega
  have hmono := certificate_bound_monotone hi
  rw [List.length_append] at hlen
  omega

theorem capped_prefix_feasibility_iff_verifier (query : List Bool) :
    query ∈ cappedPrefixFeasibilityLanguage ↔
      ∃ tail : List Bool, pair query tail ∈ cappedPrefixInequalityVerifierLanguage := by
  constructor
  · rintro ⟨inputCode,ruler,initialBits,rfl,tail,hcap,hlen,haccept⟩
    refine ⟨tail,?_⟩
    change cappedPrefixInequalityVerifier (pair (pair inputCode (pair ruler initialBits)) tail)=[true]
    apply (capped_prefix_inequality_verifier_exact _ _).mpr
    simp only [pairFst_pair,pairSnd_pair]
    exact ⟨True.intro,hcap,haccept,hlen⟩
  · rintro ⟨tail,haccept⟩
    change cappedPrefixInequalityVerifier (pair query tail)=[true] at haccept
    obtain ⟨hq,hcap,hv,hlen⟩ := (capped_prefix_inequality_verifier_exact _ _).mp haccept
    exact ⟨pairFst query,pairFst (pairSnd query),pairSnd (pairSnd query),hq,tail,hcap,hlen,hv⟩

theorem capped_prefix_feasibility_language_mem_np : cappedPrefixFeasibilityLanguage ∈ NP :=
  mem_NP_of_poly_witness certificateLengthPolynomial
    capped_prefix_inequality_verifier_language_mem_p capped_prefix_inequality_verifier_balanced
    capped_prefix_feasibility_iff_verifier

theorem capped_prefix_query_exact (inputCode ruler initialBits : List Bool) :
    pair inputCode (pair ruler initialBits) ∈ cappedPrefixFeasibilityLanguage ↔
      ∃ tail : List Bool,
        (initialBits++tail).length≤ruler.length ∧
        (initialBits++tail).length≤ inequalityInstanceLengthPolynomial inputCode.length ∧
        polynomialInequalitySystemVerifier (pair inputCode (initialBits++tail))=[true] := by
  rw [capped_prefix_feasibility_iff_verifier]
  apply exists_congr
  intro tail
  change cappedPrefixInequalityVerifier (pair (pair inputCode (pair ruler initialBits)) tail)=[true] ↔ _
  rw [capped_prefix_inequality_verifier_exact]
  simp only [pairFst_pair,pairSnd_pair,true_and]
  exact and_congr_right fun _ => and_comm

theorem unary_capped_prefix_query_exact (inputCode initialBits : List Bool) (B : ℕ)
    (hB : B≤ inequalityInstanceLengthPolynomial inputCode.length) :
    pair inputCode (pair (List.replicate B true) initialBits) ∈ cappedPrefixFeasibilityLanguage ↔
      ∃ tail : List Bool, (initialBits++tail).length≤B ∧
        polynomialInequalitySystemVerifier (pair inputCode (initialBits++tail))=[true] := by
  rw [capped_prefix_query_exact]
  simp only [List.length_replicate]
  apply exists_congr
  intro tail
  constructor
  · rintro ⟨hcap,_,haccept⟩;exact ⟨hcap,haccept⟩
  · rintro ⟨hcap,haccept⟩;exact ⟨hcap,hcap.trans hB,haccept⟩
#print axioms capped_prefix_inequality_verifier_mem_fp
#print axioms capped_prefix_inequality_verifier_exact
#print axioms capped_prefix_inequality_verifier_language_mem_p
#print axioms capped_prefix_inequality_verifier_balanced
#print axioms capped_prefix_feasibility_iff_verifier
#print axioms capped_prefix_feasibility_language_mem_np
#print axioms capped_prefix_query_exact
#print axioms unary_capped_prefix_query_exact
end IV04.Paper.InequalityFeasibilityNP
