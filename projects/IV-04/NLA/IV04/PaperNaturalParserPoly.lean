module

public import NLA.IV04.PaperNaturalParserDefinitions
public import NLA.IV04.PaperWordAdderPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem header_word_length (input : List Bool) :
    (headerWord input).length ≤ input.length := by
  induction input with
  | nil => rfl
  | cons b bits ih => cases b <;> simp [headerWord] <;> omega

theorem header_word_header (n : ℕ) (tail : List Bool) :
    headerWord (List.replicate n true ++ false :: tail)=List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ,headerWord,ih]

theorem header_word_cobham :
    Cobham fun v : Fin 1 → List Bool => headerWord (v 0) := by
  let base : (Fin 0 → List Bool) → List Bool := fun _ => []
  let zero : (Fin 2 → List Bool) → List Bool := fun _ => []
  let one : (Fin 2 → List Bool) → List Bool := fun v => true :: v 1
  have hg : Cobham base := .const []
  have hz : Cobham zero := .const []
  have ho : Cobham one :=
    (Cobham.comp (.bit true) fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hrec : ∀ (bits : List Bool) (v : Fin 0 → List Bool),
      recNotation base zero one bits v=headerWord bits := by
    intro bits v
    induction bits with
    | nil => rfl
    | cons b bits ih => cases b <;> simp [recNotation,base,zero,one,headerWord,ih]
  refine (Cobham.boundedRec hg hz ho (Cobham.proj 0) ?_).of_eq fun v => ?_
  · intro bits v
    rw [hrec]
    exact header_word_length bits
  · exact hrec (v 0) (Fin.tail v)

theorem natural_parse_rest_cobham :
    Cobham fun v : Fin 1 → List Bool => naturalParseRest (v 0) :=
  (Cobham.tailFn (Cobham.dropFn header_word_cobham (.proj 0))).of_eq fun _ => rfl

theorem natural_parse_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => naturalParseFlag (v 0) := by
  have hh := Cobham.nonemptyFn (Cobham.dropFn header_word_cobham (Cobham.proj (0 : Fin 1)))
  have hl := Cobham.notFn (Cobham.nonemptyFn
    (Cobham.dropFn natural_parse_rest_cobham header_word_cobham))
  exact (Cobham.andFn hh hl).of_eq fun _ => rfl

theorem encoded_natural_parser_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedNaturalParser (v 0) := by
  have hp := Cobham.takeFn header_word_cobham natural_parse_rest_cobham
  have ht := Cobham.dropFn header_word_cobham natural_parse_rest_cobham
  exact (Cobham.comp₂ Cobham.pairing natural_parse_flag_cobham
    (Cobham.comp₂ Cobham.pairing hp ht)).of_eq fun _ => rfl

theorem encoded_natural_parser_mem_fp : encodedNaturalParser ∈ FP :=
  CobhamFP_subset_FP encoded_natural_parser_cobham

#print axioms encoded_natural_parser_mem_fp
end IV04.Paper.Computational
