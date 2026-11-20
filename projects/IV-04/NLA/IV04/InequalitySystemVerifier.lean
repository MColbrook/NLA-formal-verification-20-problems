module

public import NLA.IV04.InequalityRowsLoop
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

def inequalitySystemRepack (input : List Bool) : List Bool :=
  pair (pairFst input) (pair (pairFst (pairSnd input)) (pairSnd (pairSnd input)))
def polynomialInequalitySystemVerifier (input : List Bool) : List Bool :=
  andBit (Cobham.eqFlag (inequalitySystemRepack input) input)
    (andBit (polynomialPayloadSyntax (pairFst (pairSnd input)))
      (andBit (polynomialWordLe [true] (pairSnd (pairSnd input)))
        (inequalityRowsVerdict (inequalityRowsState input))))

theorem inequality_rows_verdict_flag (input : List Bool) :
    inequalityRowsVerdict input=[true] ∨ inequalityRowsVerdict input=[false] := andBit_flag _ _

theorem inequality_system_verifier_flag (input : List Bool) :
    polynomialInequalitySystemVerifier input=[true] ∨ polynomialInequalitySystemVerifier input=[false] := andBit_flag _ _

theorem inequality_system_verifier_mem_fp : polynomialInequalitySystemVerifier ∈ FP := by
  have h0 := Cobham.proj (0 : Fin 1)
  have hr := Cobham.fstBlockFn h0
  have hq := Cobham.sndBlockFn h0
  have hp := Cobham.fstBlockFn hq
  have hd := Cobham.sndBlockFn hq
  have hrepack := Cobham.comp₂ Cobham.pairing hr (Cobham.comp₂ Cobham.pairing hp hd)
  have hsyntax := Cobham.comp polynomial_payload_syntax_cobham fun _ : Fin 1 => hp
  have hverdict := Cobham.andFn (Cobham.sndBlockFn (Cobham.sndBlockFn inequality_rows_state_cobham))
    (Cobham.eqFlag_mem (Cobham.fstBlockFn inequality_rows_state_cobham) (.const []))
  exact CobhamFP_subset_FP ((Cobham.andFn (Cobham.eqFlag_mem hrepack h0)
    (Cobham.andFn hsyntax (Cobham.andFn (Cobham.comp₂ polynomial_word_le_cobham (.const [true]) hd) hverdict))).of_eq fun _ => rfl)

theorem inequality_system_verifier_fields (input : List Bool) :
    polynomialInequalitySystemVerifier input=[true] ↔ inequalitySystemRepack input=input ∧
      polynomialPayloadSyntax (pairFst (pairSnd input))=[true] ∧
      0<wordValue (pairSnd (pairSnd input)) ∧
      inequalityRowsVerdict (inequalityRowsState input)=[true] := by
  unfold polynomialInequalitySystemVerifier
  rw [Cobham.andBit_eq_true_iff (Cobham.eqFlag_flag _ _) (andBit_flag _ _),
    Cobham.andBit_eq_true_iff (inequality_payload_syntax_flag _) (andBit_flag _ _),
    Cobham.andBit_eq_true_iff (by rw [polynomial_word_le_value];cases decide (wordValue [true] ≤ wordValue (pairSnd (pairSnd input))) <;> simp)
      (inequality_rows_verdict_flag _),Cobham.eqFlag_eq_true_iff]
  have hden : polynomialWordLe [true] (pairSnd (pairSnd input))=[true] ↔
      0<wordValue (pairSnd (pairSnd input)) := by
    simp [polynomial_word_le_value,wordValue,bitValue]
    omega
  rw [hden]

def decodedInequalityRow (numerators : List (List Bool)) (denominator row : List Bool) : Prop :=
  ∃ (coefficients : List (List Bool)) (bound : List Bool),
    row=pair (payloadListCode coefficients) bound ∧ coefficients.length=numerators.length ∧
      signedPayloadDot coefficients numerators ≤ signedWordValue bound*(wordValue denominator : ℤ)

theorem inequality_row_verifier_flag (input : List Bool) :
    polynomialInequalityRowVerifier input=[true] ∨ polynomialInequalityRowVerifier input=[false] := andBit_flag _ _

theorem inequality_row_at_decoded (numerators : List (List Bool)) (denominator row : List Bool) :
    inequalityRowAt (pair (pair (payloadListCode numerators) denominator) row)=[true] ↔
      0<wordValue denominator ∧ decodedInequalityRow numerators denominator row := by
  simp only [inequalityRowAt,pairFst_pair,pairSnd_pair]
  rw [Cobham.andBit_eq_true_iff (Cobham.eqFlag_flag _ _) (inequality_row_verifier_flag _),Cobham.eqFlag_eq_true_iff]
  constructor
  · rintro ⟨hcanonical,hrow⟩
    have hf := (inequality_row_verifier_fields _).mp hrow
    simp only [inequalityRowRepack,inequalityRowCoefficients,inequalityRowBound,inequalityRowNumerators,
      inequalityRowDenominator,inequalityRowPack,pairFst_pair,pairSnd_pair,true_and] at hf
    obtain ⟨hc,_,hcount,hd,hi⟩ := hf
    obtain ⟨coefficients,hcoeff⟩ := (polynomial_payload_syntax_exact _).mp hc
    have hlen : coefficients.length=numerators.length := by
      rw [←hcoeff,polynomial_payload_count_exact,polynomial_payload_count_exact] at hcount
      have he := congrArg wordValue hcount
      simpa only [word_value_foldr,IV04.Paper.bits_foldr] using he
    refine ⟨hd,coefficients,pairSnd row,?_,hlen,?_⟩
    · rw [hcoeff];exact hcanonical.symm
    · rw [←hcoeff,polynomial_signed_dot_value _ _ hlen] at hi
      exact hi
  · rintro ⟨hd,coefficients,bound,rfl,hlen,hi⟩
    refine ⟨by simp,?_⟩
    simp only [pairFst_pair,pairSnd_pair]
    apply (inequality_row_verifier_exact _).mpr
    exact ⟨coefficients,numerators,bound,denominator,rfl,hlen,hd,hi⟩

def inequalitySystemCode (rows : List (List Bool)) (numerators : List (List Bool)) (denominator : List Bool) : List Bool :=
  pair (payloadListCode rows) (pair (payloadListCode numerators) denominator)
def inequalitySystemAccepts (input : List Bool) : Prop :=
  ∃ (rows numerators : List (List Bool)) (denominator : List Bool),
    input=inequalitySystemCode rows numerators denominator ∧ 0<wordValue denominator ∧
      ∀ row ∈ rows, decodedInequalityRow numerators denominator row

theorem inequality_system_verifier_exact (input : List Bool) :
    polynomialInequalitySystemVerifier input=[true] ↔ inequalitySystemAccepts input := by
  rw [inequality_system_verifier_fields]
  constructor
  · rintro ⟨hrepack,hsyntax,hd,hrows⟩
    obtain ⟨numerators,hnum⟩ := (polynomial_payload_syntax_exact _).mp hsyntax
    obtain ⟨rows,hcode,hall⟩ := (inequality_rows_state_exact input).mp hrows
    have hquery : pairSnd input=pair (payloadListCode numerators) (pairSnd (pairSnd input)) := by
      have h := congrArg pairSnd hrepack
      simpa only [inequalitySystemRepack,pairSnd_pair,←hnum] using h.symm
    refine ⟨rows,numerators,pairSnd (pairSnd input),?_,hd,?_⟩
    · simpa only [inequalitySystemCode,inequalitySystemRepack,hcode,hnum] using hrepack.symm
    · intro row hmem
      have h := hall row hmem
      rw [hquery,inequality_row_at_decoded] at h
      exact h.2
  · rintro ⟨rows,numerators,denominator,rfl,hd,hall⟩
    refine ⟨?_,?_,?_,?_⟩
    · simp [inequalitySystemRepack,inequalitySystemCode]
    · simp only [inequalitySystemCode,pairSnd_pair,pairFst_pair]
      exact (polynomial_payload_syntax_exact _).mpr ⟨numerators,rfl⟩
    · simpa only [inequalitySystemCode,pairSnd_pair] using hd
    · rw [inequality_rows_state_exact]
      refine ⟨rows,by simp [inequalitySystemCode],?_⟩
      intro row hmem
      simp only [inequalitySystemCode,pairSnd_pair]
      rw [inequality_row_at_decoded]
      exact ⟨hd,hall row hmem⟩

theorem inequality_system_verifier_actual_polytime : polynomialInequalitySystemVerifier ∈ FP ∧
    (∀ input, polynomialInequalitySystemVerifier input=[true] ∨ polynomialInequalitySystemVerifier input=[false]) ∧
    (∀ input, polynomialInequalitySystemVerifier input=[true] ↔ inequalitySystemAccepts input) :=
  ⟨inequality_system_verifier_mem_fp,inequality_system_verifier_flag,inequality_system_verifier_exact⟩
#print axioms inequality_system_verifier_actual_polytime
end IV04.Paper.Computational
