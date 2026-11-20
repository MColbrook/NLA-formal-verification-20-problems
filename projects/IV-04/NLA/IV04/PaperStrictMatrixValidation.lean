module

public import NLA.IV04.PaperStrictMatrixValidationDefinitions
public import NLA.IV04.PaperOrderedMatrixVertexSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem strict_matrix_selection_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => strictMatrixSelectionFlag (v 0) := by
  have h0 := Cobham.proj (0 : Fin 1)
  have h1 := Cobham.sndBlockFn h0
  have h2 := Cobham.sndBlockFn h1
  have h3 := Cobham.sndBlockFn h2
  have hb := Cobham.fstBlockFn h3
  have hr := Cobham.sndBlockFn hb
  have ht := Cobham.sndBlockFn h3
  have hc := Cobham.sndBlockFn hr
  have hf := Cobham.sndBlockFn (Cobham.fstBlockFn hr)
  exact (Cobham.andFn (Cobham.fstBlockFn h0)
    (Cobham.andFn (Cobham.notFn (Cobham.nonemptyFn ht))
      (Cobham.andFn (Cobham.notFn (Cobham.nonemptyFn hc))
        (Cobham.notFn (Cobham.nonemptyFn hf))))).of_eq fun _ => rfl

theorem strict_matrix_selection_flag_mem_fp : strictMatrixSelectionFlag ∈ FP :=
  CobhamFP_subset_FP strict_matrix_selection_flag_cobham

theorem encoded_strict_matrix_selection_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedStrictMatrixSelectionFlag (v 0) :=
  (Cobham.comp strict_matrix_selection_flag_cobham
    fun _ : Fin 1 => encoded_ordered_matrix_vertex_selection_cobham).of_eq fun _ => rfl

theorem encoded_strict_matrix_selection_flag_mem_fp : encodedStrictMatrixSelectionFlag ∈ FP :=
  CobhamFP_subset_FP encoded_strict_matrix_selection_flag_cobham

theorem strict_matrix_selection_flag_code (b : Bool)
    (dimension denominator words threshold fieldsTail choices tail : List Bool) :
    strictMatrixSelectionFlag
      (pair [b] (pair dimension (pair denominator
        (pair (pair words (pair (pair threshold fieldsTail) choices)) tail))))=
      [decide (b=true ∧ tail=[] ∧ choices=[] ∧ fieldsTail=[])] := by
  cases b <;> cases tail <;> cases choices <;> cases fieldsTail <;>
    simp [strictMatrixSelectionFlag,pairFst_pair,pairSnd_pair,
      andBit,notBit,nonemptyFlag,caseBit₀,caseBit]

theorem strict_matrix_selection_flag_decode_failure (matrix choices : List Bool)
    (h : readMatrixRationals matrix=none) :
    encodedStrictMatrixSelectionFlag (pair matrix choices)=[false] := by
  have hf := ordered_matrix_vertex_selection_decode_failure matrix choices h
  simp [encodedStrictMatrixSelectionFlag,strictMatrixSelectionFlag,hf,andBit,caseBit₀]

theorem strict_matrix_selection_rational_input (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) (horder : ∀ row ∈ pairs, row.1 ≤ row.2)
    (hchoices : n*n ≤ choices.length) :
    encodedStrictMatrixSelectionFlag (pair matrix choices)=
      [decide (tail=[] ∧ choices.length=n*n)] := by
  obtain ⟨dimension,denominator,rows,thresholdWord,_,_,_,_,_,hout⟩ :=
    ordered_matrix_vertex_selection_rational_input matrix choices tail n pairs threshold hread hsize horder hchoices
  rw [encodedStrictMatrixSelectionFlag,hout]
  change strictMatrixSelectionFlag
    (pair [true] (pair dimension (pair denominator
      (pair (pair (payloadListCode (selectedEndpointWords rows choices))
        (pair (pair thresholdWord []) (choices.drop (n*n)))) tail))))=_
  rw [strict_matrix_selection_flag_code]
  simp only [true_and, and_true]
  have hd : choices.drop (n*n)=[] ↔ choices.length=n*n := by
    rw [List.drop_eq_nil_iff]
    omega
  simp only [hd]

#print axioms strict_matrix_selection_rational_input
end IV04.Paper.Computational
