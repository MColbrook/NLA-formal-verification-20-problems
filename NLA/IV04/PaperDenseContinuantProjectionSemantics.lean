module

public import NLA.IV04.PaperDenseContinuantProjectionBounds
public import NLA.IV04.PaperDenseContinuantProjectionReference
public import NLA.IV04.PaperPayloadLookupSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem row_projection_diagonal_index_value (d i : List Bool) :
    wordValue (rowProjectionDiagonalIndex d i)=wordValue i*wordValue d+wordValue i := by
  simp [rowProjectionDiagonalIndex,canonical_word_value,polynomial_word_add_value,canonical_word_multiply_value]

theorem row_projection_lower_index_value (d i : List Bool) :
    wordValue (rowProjectionLowerIndex d i)=wordValue i*wordValue d+(wordValue i-1) := by
  simp [rowProjectionLowerIndex,canonical_word_value,polynomial_word_add_value,canonical_word_multiply_value,decrement_count_value]

theorem row_projection_previous_upper_index_value (d i : List Bool) :
    wordValue (rowProjectionPreviousUpperIndex d i)=(wordValue i-1)*wordValue d+wordValue i := by
  simp [rowProjectionPreviousUpperIndex,canonical_word_value,polynomial_word_add_value,canonical_word_multiply_value,decrement_count_value]

theorem payload_lookup_word_getD (rows : List (List Bool)) (index : List Bool) :
    polynomialPayloadLookup (pair index (payloadListCode rows))=rows.getD (wordValue index) [] := by
  by_cases hr : wordValue index < rows.length
  · rw [payload_lookup_word_code rows index hr]
    exact List.getElem_eq_getD (h := hr) []
  · rw [payload_lookup_word_past_end rows index (Nat.le_of_not_gt hr)]
    simp [List.getD, hr]

theorem row_projection_row_code (d i : List Bool) (words : List (List Bool)) :
    rowProjectionRow d i (payloadListCode words)=rowProjectionReferenceRow (wordValue d) (wordValue i) words := by
  simp only [rowProjectionRow,payload_lookup_word_getD,row_projection_diagonal_index_value,
    row_projection_lower_index_value,row_projection_previous_upper_index_value,canonical_nonempty_flag]
  by_cases hz : wordValue i=0 <;> simp [hz,rowProjectionReferenceRow,caseBit₀]

#print axioms row_projection_row_code
end IV04.Paper.Computational
