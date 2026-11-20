module

public import NLA.IV04.InequalitySystemVerifier
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem inequality_payload_code_injective : Function.Injective payloadListCode := by
  intro left
  induction left with
  | nil =>
    intro right h
    cases right with
    | nil => rfl
    | cons p ps => exact (payload_pair_ne_nil p (payloadListCode ps) h.symm).elim
  | cons p ps ih =>
    intro right h
    cases right with
    | nil => exact (payload_pair_ne_nil p (payloadListCode ps) h).elim
    | cons q qs =>
      have hp := congrArg pairFst h
      have ht := congrArg pairSnd h
      simp only [payloadListCode,pairFst_pair] at hp
      simp only [payloadListCode,pairSnd_pair] at ht
      exact congrArg₂ List.cons hp (ih ht)

theorem inequality_rows_state_code (rows numerators : List (List Bool)) (denominator : List Bool) :
    inequalityRowsVerdict (inequalityRowsState (inequalitySystemCode rows numerators denominator))=[true] ↔
      ∀ row ∈ rows, inequalityRowAt (pair (pair (payloadListCode numerators) denominator) row)=[true] := by
  rw [inequality_rows_state_exact]
  simp only [inequalitySystemCode,pairFst_pair,pairSnd_pair]
  constructor
  · rintro ⟨rs,hcode,hall⟩
    have he : rs=rows := inequality_payload_code_injective hcode
    simpa only [he] using hall
  · intro hall;exact ⟨rows,rfl,hall⟩

theorem inequality_system_verifier_code (rows numerators : List (List Bool)) (denominator : List Bool) :
    polynomialInequalitySystemVerifier (inequalitySystemCode rows numerators denominator)=[true] ↔
      0<wordValue denominator ∧ ∀ row ∈ rows, decodedInequalityRow numerators denominator row := by
  rw [inequality_system_verifier_fields]
  have hsyntax : polynomialPayloadSyntax (payloadListCode numerators)=[true] :=
    (polynomial_payload_syntax_exact _).mpr ⟨numerators,rfl⟩
  simp only [inequalitySystemRepack,inequalitySystemCode,pairFst_pair,pairSnd_pair,hsyntax,true_and]
  change (0<wordValue denominator ∧ inequalityRowsVerdict (inequalityRowsState (inequalitySystemCode rows numerators denominator))=[true]) ↔ _
  rw [inequality_rows_state_code]
  constructor
  · rintro ⟨hd,hall⟩
    refine ⟨hd,?_⟩
    intro row hmem;exact ((inequality_row_at_decoded numerators denominator row).mp (hall row hmem)).2
  · rintro ⟨hd,hall⟩
    refine ⟨hd,?_⟩
    intro row hmem;exact (inequality_row_at_decoded numerators denominator row).mpr ⟨hd,hall row hmem⟩

theorem decoded_inequality_row_code (coefficients numerators : List (List Bool)) (bound denominator : List Bool) :
    decodedInequalityRow numerators denominator (pair (payloadListCode coefficients) bound) ↔
      coefficients.length=numerators.length ∧
        signedPayloadDot coefficients numerators ≤ signedWordValue bound*(wordValue denominator : ℤ) := by
  constructor
  · rintro ⟨cs,b,he,hcount,hi⟩
    have hc := congrArg pairFst he
    have hb := congrArg pairSnd he
    simp only [pairFst_pair] at hc
    simp only [pairSnd_pair] at hb
    have hcs : coefficients=cs := inequality_payload_code_injective hc
    simpa only [←hcs,←hb] using And.intro hcount hi
  · rintro ⟨hcount,hi⟩;exact ⟨coefficients,bound,rfl,hcount,hi⟩

def inequalityTypedSystemCode (rows : List (List (List Bool) × List Bool))
    (numerators : List (List Bool)) (denominator : List Bool) : List Bool :=
  inequalitySystemCode (rows.map (fun row => pair (payloadListCode row.1) row.2)) numerators denominator

theorem inequality_typed_system_verifier_exact (rows : List (List (List Bool) × List Bool))
    (numerators : List (List Bool)) (denominator : List Bool) :
    polynomialInequalitySystemVerifier (inequalityTypedSystemCode rows numerators denominator)=[true] ↔
      0<wordValue denominator ∧ ∀ row ∈ rows, row.1.length=numerators.length ∧
        signedPayloadDot row.1 numerators ≤ signedWordValue row.2*(wordValue denominator : ℤ) := by
  rw [inequalityTypedSystemCode,inequality_system_verifier_code]
  constructor
  · rintro ⟨hd,hall⟩
    refine ⟨hd,?_⟩
    intro row hmem
    exact (decoded_inequality_row_code row.1 numerators row.2 denominator).mp
      (hall _ (List.mem_map.mpr ⟨row,hmem,rfl⟩))
  · rintro ⟨hd,hall⟩
    refine ⟨hd,?_⟩
    intro encoded hmem
    obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hmem
    exact (decoded_inequality_row_code row.1 numerators row.2 denominator).mpr (hall row hrow)

def inequalityIntegerWord (z : ℤ) : List Bool := decide (z<0) :: z.natAbs.bits
private theorem inequality_word_bits (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr];exact IV04.Paper.bits_foldr n

theorem inequality_integer_word_value (z : ℤ) : signedWordValue (inequalityIntegerWord z)=z := by
  cases z <;> simp [inequalityIntegerWord,signedWordValue,firstBit,inequality_word_bits]
  omega

theorem inequality_integer_word_length (z : ℤ) : (inequalityIntegerWord z).length=z.natAbs.size+1 := by
  simp only [inequalityIntegerWord,List.length_cons,←Nat.size_eq_bits_len]

theorem inequality_payload_list_code_length (payloads : List (List Bool)) :
    (payloadListCode payloads).length=2*(payloads.map List.length).sum+2*payloads.length := by
  induction payloads with
  | nil => rfl
  | cons p ps ih =>
    simp only [payloadListCode,pair_length,List.map_cons,List.sum_cons,List.length_cons,ih]
    omega

def inequalityIntegerDot : List ℤ → List ℤ → ℤ
  | a::as,p::ps => a*p+inequalityIntegerDot as ps
  | _,_ => 0

theorem signed_payload_dot_integer_map (coefficients numerators : List ℤ) :
    signedPayloadDot (coefficients.map inequalityIntegerWord) (numerators.map inequalityIntegerWord)=
      inequalityIntegerDot coefficients numerators := by
  induction coefficients generalizing numerators with
  | nil => cases numerators <;> rfl
  | cons a as ih =>
    cases numerators with
    | nil => rfl
    | cons p ps => simp [signedPayloadDot,inequalityIntegerDot,inequality_integer_word_value,ih]

def inequalityIntegerSystemCode (rows : List (List ℤ × ℤ)) (numerators : List ℤ) (denominator : ℕ) : List Bool :=
  inequalityTypedSystemCode (rows.map (fun row => (row.1.map inequalityIntegerWord,inequalityIntegerWord row.2)))
    (numerators.map inequalityIntegerWord) denominator.bits

theorem inequality_integer_system_verifier_exact (rows : List (List ℤ × ℤ))
    (numerators : List ℤ) (denominator : ℕ) :
    polynomialInequalitySystemVerifier (inequalityIntegerSystemCode rows numerators denominator)=[true] ↔
      0<denominator ∧ ∀ row ∈ rows, row.1.length=numerators.length ∧
        inequalityIntegerDot row.1 numerators ≤ row.2*(denominator : ℤ) := by
  rw [inequalityIntegerSystemCode,inequality_typed_system_verifier_exact,inequality_word_bits]
  constructor
  · rintro ⟨hd,hall⟩
    refine ⟨hd,?_⟩
    intro row hmem
    have h := hall (row.1.map inequalityIntegerWord,inequalityIntegerWord row.2) (List.mem_map.mpr ⟨row,hmem,rfl⟩)
    simpa only [List.length_map,signed_payload_dot_integer_map,inequality_integer_word_value] using h
  · rintro ⟨hd,hall⟩
    refine ⟨hd,?_⟩
    intro encoded hmem
    obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hmem
    simpa only [List.length_map,signed_payload_dot_integer_map,inequality_integer_word_value] using hall row hrow

theorem inequality_integer_verifier_actual_polytime : polynomialInequalitySystemVerifier ∈ FP ∧
    (∀ input, polynomialInequalitySystemVerifier input=[true] ↔ inequalitySystemAccepts input) ∧
    (∀ (rows : List (List ℤ × ℤ)) (numerators : List ℤ) (denominator : ℕ),
      polynomialInequalitySystemVerifier (inequalityIntegerSystemCode rows numerators denominator)=[true] ↔
        0<denominator ∧ ∀ row ∈ rows, row.1.length=numerators.length ∧
          inequalityIntegerDot row.1 numerators ≤ row.2*(denominator : ℤ)) :=
  ⟨inequality_system_verifier_mem_fp,inequality_system_verifier_exact,inequality_integer_system_verifier_exact⟩
#print axioms inequality_integer_verifier_actual_polytime
end IV04.Paper.Computational
