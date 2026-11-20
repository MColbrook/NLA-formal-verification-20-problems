module

public import NLA.IV04.InequalityPayloadSyntax
public import NLA.IV04.PaperSignedOrderPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem polynomial_signed_le_flag (left right : List Bool) :
    polynomialSignedLe left right=[true] ∨ polynomialSignedLe left right=[false] := by
  rw [polynomial_signed_le_value]
  cases decide (signedWordValue left ≤ signedWordValue right) <;> simp

theorem polynomial_signed_le_correct (left right : List Bool) :
    polynomialSignedLe left right=[true] ↔ signedWordValue left ≤ signedWordValue right := by
  simp [polynomial_signed_le_value]

theorem inequality_payload_syntax_flag (input : List Bool) :
    polynomialPayloadSyntax input=[true] ∨ polynomialPayloadSyntax input=[false] :=
  andBit_flag _ _

def inequalityRowPack (coefficients bound numerators denominator : List Bool) : List Bool :=
  pair coefficients (pair bound (pair numerators denominator))
def inequalityRowCode (coefficients : List (List Bool)) (bound : List Bool)
    (numerators : List (List Bool)) (denominator : List Bool) : List Bool :=
  inequalityRowPack (payloadListCode coefficients) bound (payloadListCode numerators) denominator

def inequalityRowCoefficients (input : List Bool) : List Bool := pairFst input
def inequalityRowBound (input : List Bool) : List Bool := pairFst (pairSnd input)
def inequalityRowNumerators (input : List Bool) : List Bool := pairFst (pairSnd (pairSnd input))
def inequalityRowDenominator (input : List Bool) : List Bool := pairSnd (pairSnd (pairSnd input))
def inequalityRowRepack (input : List Bool) : List Bool :=
  inequalityRowPack (inequalityRowCoefficients input) (inequalityRowBound input)
    (inequalityRowNumerators input) (inequalityRowDenominator input)
def inequalityRowArithmetic (input : List Bool) : List Bool :=
  polynomialSignedLe
    (polynomialSignedDot (pair (inequalityRowCoefficients input) (inequalityRowNumerators input)))
    (polynomialSignedMultiply (inequalityRowBound input) (false::inequalityRowDenominator input))

def polynomialInequalityRowVerifier (input : List Bool) : List Bool :=
  andBit (Cobham.eqFlag (inequalityRowRepack input) input)
    (andBit (polynomialPayloadSyntax (inequalityRowCoefficients input))
      (andBit (polynomialPayloadSyntax (inequalityRowNumerators input))
        (andBit (Cobham.eqFlag (polynomialPayloadCount (inequalityRowCoefficients input))
            (polynomialPayloadCount (inequalityRowNumerators input)))
          (andBit (polynomialWordLe [true] (inequalityRowDenominator input)) (inequalityRowArithmetic input)))))

theorem inequality_row_arithmetic_flag (input : List Bool) :
    inequalityRowArithmetic input=[true] ∨ inequalityRowArithmetic input=[false] :=
  polynomial_signed_le_flag _ _

theorem inequality_row_verifier_mem_fp : polynomialInequalityRowVerifier ∈ FP := by
  have h0 := Cobham.proj (0 : Fin 1)
  have hc := Cobham.fstBlockFn h0
  have hb := Cobham.fstBlockFn (Cobham.sndBlockFn h0)
  have hp := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn h0))
  have hd := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn h0))
  have hrepack := Cobham.comp₂ Cobham.pairing hc
    (Cobham.comp₂ Cobham.pairing hb (Cobham.comp₂ Cobham.pairing hp hd))
  have hsyntaxc := Cobham.comp polynomial_payload_syntax_cobham fun _ : Fin 1 => hc
  have hsyntaxp := Cobham.comp polynomial_payload_syntax_cobham fun _ : Fin 1 => hp
  have hcountc := Cobham.comp polynomial_payload_count_cobham fun _ : Fin 1 => hc
  have hcountp := Cobham.comp polynomial_payload_count_cobham fun _ : Fin 1 => hp
  have hdot := Cobham.comp (FP_subset_CobhamFP polynomial_signed_dot_mem_fp) fun _ : Fin 1 =>
    Cobham.comp₂ Cobham.pairing hc hp
  have hsden := Cobham.comp (Cobham.bit false) fun _ : Fin 1 => hd
  have hbound := Cobham.comp₂ polynomial_signed_multiply_cobham hb hsden
  have hineq := Cobham.comp₂ polynomial_signed_le_cobham hdot hbound
  exact CobhamFP_subset_FP ((Cobham.andFn (Cobham.eqFlag_mem hrepack h0)
    (Cobham.andFn hsyntaxc (Cobham.andFn hsyntaxp (Cobham.andFn (Cobham.eqFlag_mem hcountc hcountp)
      (Cobham.andFn (Cobham.comp₂ polynomial_word_le_cobham (.const [true]) hd) hineq))))).of_eq fun _ => rfl)

theorem inequality_row_verifier_fields (input : List Bool) :
    polynomialInequalityRowVerifier input=[true] ↔
      inequalityRowRepack input=input ∧
      polynomialPayloadSyntax (inequalityRowCoefficients input)=[true] ∧
      polynomialPayloadSyntax (inequalityRowNumerators input)=[true] ∧
      polynomialPayloadCount (inequalityRowCoefficients input)=polynomialPayloadCount (inequalityRowNumerators input) ∧
      0<wordValue (inequalityRowDenominator input) ∧
      signedWordValue (polynomialSignedDot (pair (inequalityRowCoefficients input) (inequalityRowNumerators input))) ≤
        signedWordValue (inequalityRowBound input)*(wordValue (inequalityRowDenominator input) : ℤ) := by
  unfold polynomialInequalityRowVerifier
  rw [Cobham.andBit_eq_true_iff (Cobham.eqFlag_flag _ _) (andBit_flag _ _),
    Cobham.andBit_eq_true_iff (inequality_payload_syntax_flag _) (andBit_flag _ _),
    Cobham.andBit_eq_true_iff (inequality_payload_syntax_flag _) (andBit_flag _ _),
    Cobham.andBit_eq_true_iff (Cobham.eqFlag_flag _ _) (andBit_flag _ _),
    Cobham.andBit_eq_true_iff (by rw [polynomial_word_le_value];cases decide (wordValue [true] ≤ wordValue (inequalityRowDenominator input)) <;> simp)
      (inequality_row_arithmetic_flag input)]
  simp only [Cobham.eqFlag_eq_true_iff]
  have hden : polynomialWordLe [true] (inequalityRowDenominator input)=[true] ↔
      0<wordValue (inequalityRowDenominator input) := by
    simp [polynomial_word_le_value,wordValue,bitValue]
    omega
  rw [hden,inequalityRowArithmetic,polynomial_signed_le_correct,polynomial_signed_multiply_value,
    positive_signed_word_value]

def inequalityRowAccepts (input : List Bool) : Prop :=
  ∃ (coefficients numerators : List (List Bool)) (bound denominator : List Bool),
    input=inequalityRowCode coefficients bound numerators denominator ∧
    coefficients.length=numerators.length ∧ 0<wordValue denominator ∧
    signedPayloadDot coefficients numerators ≤ signedWordValue bound*(wordValue denominator : ℤ)

theorem inequality_row_verifier_exact (input : List Bool) :
    polynomialInequalityRowVerifier input=[true] ↔ inequalityRowAccepts input := by
  rw [inequality_row_verifier_fields]
  constructor
  · rintro ⟨hrepack,hc,hp,hcount,hd,hi⟩
    obtain ⟨coefficients,hcoeff⟩ := (polynomial_payload_syntax_exact _).mp hc
    obtain ⟨numerators,hnum⟩ := (polynomial_payload_syntax_exact _).mp hp
    have hlen : coefficients.length=numerators.length := by
      rw [←hcoeff,←hnum,polynomial_payload_count_exact,polynomial_payload_count_exact] at hcount
      have he := congrArg wordValue hcount
      simpa only [word_value_foldr,IV04.Paper.bits_foldr] using he
    refine ⟨coefficients,numerators,inequalityRowBound input,inequalityRowDenominator input,?_,hlen,hd,?_⟩
    · simpa only [inequalityRowCode,inequalityRowRepack,hcoeff,hnum] using hrepack.symm
    · rw [←hcoeff,←hnum,polynomial_signed_dot_value _ _ hlen] at hi
      exact hi
  · rintro ⟨coefficients,numerators,bound,denominator,rfl,hlen,hd,hi⟩
    have hc : inequalityRowCoefficients (inequalityRowCode coefficients bound numerators denominator)=payloadListCode coefficients := by
      simp [inequalityRowCoefficients,inequalityRowCode,inequalityRowPack]
    have hp : inequalityRowNumerators (inequalityRowCode coefficients bound numerators denominator)=payloadListCode numerators := by
      simp [inequalityRowNumerators,inequalityRowCode,inequalityRowPack]
    have hb : inequalityRowBound (inequalityRowCode coefficients bound numerators denominator)=bound := by
      simp [inequalityRowBound,inequalityRowCode,inequalityRowPack]
    have hden : inequalityRowDenominator (inequalityRowCode coefficients bound numerators denominator)=denominator := by
      simp [inequalityRowDenominator,inequalityRowCode,inequalityRowPack]
    refine ⟨?_,?_,?_,?_,by simpa only [hden] using hd,?_⟩
    · simp [inequalityRowRepack,inequalityRowCode,inequalityRowPack,inequalityRowCoefficients,
        inequalityRowBound,inequalityRowNumerators,inequalityRowDenominator]
    · rw [hc,polynomial_payload_syntax_exact];exact ⟨coefficients,rfl⟩
    · rw [hp,polynomial_payload_syntax_exact];exact ⟨numerators,rfl⟩
    · rw [hc,hp,polynomial_payload_count_exact,polynomial_payload_count_exact,hlen]
    · simpa only [hc,hp,hb,hden,polynomial_signed_dot_value _ _ hlen] using hi

theorem inequality_row_verifier_actual_polytime : polynomialInequalityRowVerifier ∈ FP ∧
    ∀ input, polynomialInequalityRowVerifier input=[true] ↔ inequalityRowAccepts input :=
  ⟨inequality_row_verifier_mem_fp,inequality_row_verifier_exact⟩
#print axioms inequality_row_verifier_actual_polytime
end IV04.Paper.Computational
