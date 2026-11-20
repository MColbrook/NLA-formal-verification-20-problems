module

public import NLA.IV04.PaperSATRawLiteralDefinitions
public import NLA.IV04.PaperLengthWord
public import NLA.IV04.PaperWordAdderSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem sat_unary_flag_length (bits : List Bool) : (satUnaryFlag bits).length=1 := by
  induction bits with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [satUnaryFlag,ih]

theorem sat_unary_flag_exact (bits : List Bool) :
    satUnaryFlag bits=[decide (∀ b∈bits,b=true)] := by
  induction bits with
  | nil => simp [satUnaryFlag]
  | cons b bits ih => cases b <;> simp [satUnaryFlag,ih]

theorem sat_unary_flag_cobham : Cobham fun v : Fin 1 → List Bool => satUnaryFlag (v 0) := by
  let base : (Fin 0 → List Bool) → List Bool := fun _ => [true]
  let zero : (Fin 2 → List Bool) → List Bool := fun _ => [false]
  let one : (Fin 2 → List Bool) → List Bool := fun v => v 1
  have hg : Cobham base := .const [true]
  have hz : Cobham zero := .const [false]
  have ho : Cobham one := .proj 1
  have hrec : ∀ (bits : List Bool) (v : Fin 0 → List Bool),
      recNotation base zero one bits v=satUnaryFlag bits := by
    intro bits v
    induction bits with
    | nil => rfl
    | cons b bits ih => cases b <;> simp [recNotation,base,zero,one,satUnaryFlag,ih]
  refine (Cobham.boundedRec hg hz ho (Cobham.const [true]) ?_).of_eq fun v => ?_
  · intro bits v
    rw [hrec,sat_unary_flag_length]
    exact Nat.le_refl 1
  · exact hrec (v 0) (Fin.tail v)

theorem polynomial_sat_raw_literal_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATRawLiteral (v 0) := by
  have hu := Cobham.comp sat_unary_flag_cobham fun _ : Fin 1 => Cobham.tailFn (Cobham.proj (0 : Fin 1))
  have hv := Cobham.comp input_length_word_cobham fun _ : Fin 1 => Cobham.tailFn (Cobham.proj (0 : Fin 1))
  have hf := Cobham.andFn (Cobham.nonemptyFn (Cobham.proj (0 : Fin 1))) hu
  exact (Cobham.comp₂ Cobham.pairing hf
    (Cobham.comp₂ Cobham.pairing hv (Cobham.headFlagFn (.proj 0)))).of_eq fun _ => rfl

theorem polynomial_sat_raw_literal_mem_fp : polynomialSATRawLiteral ∈ FP :=
  CobhamFP_subset_FP polynomial_sat_raw_literal_cobham

theorem actual_sat_raw_literal_decoder (input : List Bool) :
    decodeSATRawLiteralResult input=Complexity.SAT.Lit.decodeRaw? input := by
  cases input with
  | nil => simp [decodeSATRawLiteralResult,polynomialSATRawLiteral,
      Complexity.SAT.Lit.decodeRaw?,nonemptyFlag,andBit,caseBit₀,caseBit]
  | cons sign rest =>
    by_cases h : ∀ b∈rest,b=true
    · have hf : satUnaryFlag rest=[true] := by
        simpa only [sat_unary_flag_exact,List.cons.injEq,and_true,decide_eq_true_eq] using h
      have hd : Complexity.SAT.Lit.decodeRaw? (sign::rest)=some ⟨sign,rest.length⟩ := by
        simp only [Complexity.SAT.Lit.decodeRaw?,dif_pos h]
      rw [hd]
      cases sign <;> simp [decodeSATRawLiteralResult,polynomialSATRawLiteral,hf,
        nonemptyFlag,andBit,caseBit₀,caseBit,input_length_word_value,firstBit]
    · have hf : satUnaryFlag rest=[false] := by
        simpa only [sat_unary_flag_exact,List.cons.injEq,and_true,decide_eq_false_iff_not] using h
      have hd : Complexity.SAT.Lit.decodeRaw? (sign::rest)=none := by
        simp only [Complexity.SAT.Lit.decodeRaw?,dif_neg h]
      rw [hd]
      cases sign <;> simp [decodeSATRawLiteralResult,polynomialSATRawLiteral,hf,
        nonemptyFlag,andBit,caseBit₀,caseBit]

theorem polynomial_sat_raw_literal_encoded (lit : Complexity.SAT.Lit) :
    polynomialSATRawLiteral lit.encodeRaw=pair [true] (pair lit.var.bits [lit.sign]) := by
  rcases lit with ⟨sign,varIndex⟩
  cases sign <;> simp [polynomialSATRawLiteral,Complexity.SAT.Lit.encodeRaw,Complexity.SAT.Unary.encode,
    sat_unary_flag_exact,input_length_word_exact,
    nonemptyFlag,andBit,caseBit₀,caseBit]

theorem sat_raw_literal_actual_polytime : polynomialSATRawLiteral ∈ FP ∧
    (∀ input, decodeSATRawLiteralResult input=Complexity.SAT.Lit.decodeRaw? input) ∧
    (∀ lit : Complexity.SAT.Lit,
      polynomialSATRawLiteral lit.encodeRaw=pair [true] (pair lit.var.bits [lit.sign])) :=
  ⟨polynomial_sat_raw_literal_mem_fp,actual_sat_raw_literal_decoder,polynomial_sat_raw_literal_encoded⟩

#print axioms sat_unary_flag_exact
#print axioms polynomial_sat_raw_literal_mem_fp
#print axioms actual_sat_raw_literal_decoder
#print axioms polynomial_sat_raw_literal_encoded
#print axioms sat_raw_literal_actual_polytime
end IV04.Paper.Computational
