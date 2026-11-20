module

public import NLA.IV04.PaperSATLiteralDigitsSemantics
public import NLA.IV04.PaperWordListHornerInput
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction
 theorem literal_digits_of_fn_range (n : ℕ) (f : ℕ → List Bool) :
    List.ofFn (fun i : Fin n => f i.val)=(List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj;simp
 theorem sat_literal_positional_payloads (formula : SAT.CNF) (v : Fin (satVariables formula)) (b : Bool) :
    positionalDigitPayloads (fun k => satWeightDigits formula (Sum.inl (v,b)) (finSumFinEquiv.symm k))=
      ((formula.map fun clause => (literalCount clause v.val b).bits).reverse) ++
        (((List.range (satVariables formula)).map fun i => if i=v.val then [true] else []).reverse) := by
  have hd : (fun k => satWeightDigits formula (Sum.inl (v,b)) (finSumFinEquiv.symm k))=
      Fin.append (fun u : Fin (satVariables formula) => if v=u then 1 else 0)
        (fun j : Fin formula.length => literalCount (satClause formula j) v.val b) := by
    funext k
    refine Fin.addCases ?_ ?_ k
    · intro u;simp [satWeightDigits]
    · intro j;simp [satWeightDigits]
  have hm : (fun u : Fin (satVariables formula) => (if v=u then 1 else 0).bits)=
      (fun u : Fin (satVariables formula) => if u.val=v.val then [true] else []) := by
    funext u
    by_cases h : v=u
    · subst u;simp
    · have hn : u.val≠v.val := by intro he;exact h (Fin.ext he.symm)
      simp [h,hn]
  simp only [positionalDigitPayloads,hd,List.ofFn_fin_append,List.reverse_append,List.map_append,
    List.map_reverse,List.map_ofFn]
  simp only [Function.comp_def]
  rw [hm,literal_digits_of_fn_range (satVariables formula) (fun i : ℕ => if i=v.val then [true] else [])]
  congr 1
  congr 1
  simpa only [satClause,Fin.getElem_fin] using (List.ofFn_getElem_eq_map formula (fun clause => (literalCount clause v.val b).bits))
 theorem polynomial_sat_literal_digits_positional (bits : List Bool) (formula : SAT.CNF)
    (v : Fin (satVariables formula)) (b : Bool) (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATLiteralDigits (pair bits (pair v.val.bits [b]))=
      payloadListCode (positionalDigitPayloads
        (fun k => satWeightDigits formula (Sum.inl (v,b)) (finSumFinEquiv.symm k))) := by
  rw [polynomial_sat_literal_digits_exact bits formula v.val b h,sat_literal_positional_payloads]
 theorem polynomial_sat_literal_weight_exact (bits : List Bool) (formula : SAT.CNF)
    (v : Fin (satVariables formula)) (b : Bool) (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATLiteralWeight (pair bits (pair v.val.bits [b]))=
      (satSubsetWeights formula (Sum.inl (v,b))).bits := by
  simp only [polynomialSATLiteralWeight,pairFst_pair,polynomial_sat_cnf_parse_exact bits formula h,
    pairSnd_pair,polynomial_sat_digit_base_exact,polynomial_sat_literal_digits_positional bits formula v b h]
  change canonicalWord (polynomialWordListHorner (actualSATWeightHornerInput formula (Sum.inl (v,b))))=_
  rw [canonical_word_eq_bits,actual_sat_weight_horner_word_value]
 theorem sat_literal_weight_actual_polytime : polynomialSATLiteralWeight ∈ FP ∧
    ∀ (bits : List Bool) (formula : SAT.CNF) (v : Fin (satVariables formula)) (b : Bool),
      SAT.CNF.decode? bits=some formula →
        polynomialSATLiteralWeight (pair bits (pair v.val.bits [b]))=
          (satSubsetWeights formula (Sum.inl (v,b))).bits :=
  ⟨polynomial_sat_literal_weight_mem_fp,polynomial_sat_literal_weight_exact⟩
#print axioms polynomial_sat_literal_digits_positional
#print axioms polynomial_sat_literal_weight_exact
#print axioms sat_literal_weight_actual_polytime
end IV04.Paper.Computational
