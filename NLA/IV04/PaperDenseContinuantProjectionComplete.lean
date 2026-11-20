module

public import NLA.IV04.PaperDenseContinuantProjectionSemantics
public import NLA.IV04.PaperPayloadReverseSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem row_projection_finished_iterate (k : ℕ) (d i fields output : List Bool)
    (h : wordValue d ≤ wordValue i) :
    (rowProjectionStep^[k]) (rowProjectionPack d i fields output)=rowProjectionPack d i fields output := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,row_projection_step_pack,polynomial_word_le_value]
    simp [h,caseBit₀]

theorem row_projection_prefix (k n : ℕ) (words : List (List Bool)) (d : List Bool)
    (hd : wordValue d=n) (hk : k ≤ n) :
    ∃ i : List Bool, wordValue i=k ∧
      (rowProjectionStep^[k]) (rowProjectionPack d [] (payloadListCode words) [])=
        rowProjectionPack d i (payloadListCode words)
          (payloadListCode (((List.range k).map (fun j => rowProjectionReferenceRow n j words)).reverse)) := by
  induction k with
  | zero => exact ⟨[],rfl,rfl⟩
  | succ k ih =>
    obtain ⟨i,hi,he⟩ := ih (by omega)
    let next := canonicalWord (polynomialWordAdd i [true])
    have hn : wordValue next=k+1 := by
      simp [next,canonical_word_value,polynomial_word_add_value,hi,wordValue,bitValue]
    refine ⟨next,hn,?_⟩
    rw [Function.iterate_succ_apply',he,row_projection_step_pack,polynomial_word_le_value]
    have hstop : ¬ wordValue d ≤ wordValue i := by rw [hd,hi];omega
    simp only [hstop,decide_false,caseBit₀]
    rw [row_projection_row_code,hd,hi]
    simp only [List.range_succ,List.map_append,List.map_singleton,List.reverse_append,
      List.reverse_singleton,List.singleton_append,payloadListCode]
    rfl

theorem row_projection_complete (k n : ℕ) (words : List (List Bool)) (d : List Bool)
    (hd : wordValue d=n) (hk : n ≤ k) :
    ∃ i : List Bool, wordValue i=n ∧
      (rowProjectionStep^[k]) (rowProjectionPack d [] (payloadListCode words) [])=
        rowProjectionPack d i (payloadListCode words)
          (payloadListCode (denseContinuantReferenceRows n words).reverse) := by
  obtain ⟨i,hi,he⟩ := row_projection_prefix n n words d hd (by omega)
  refine ⟨i,hi,?_⟩
  rw [show k=(k-n)+n by omega,Function.iterate_add_apply,he]
  exact row_projection_finished_iterate (k-n) d i (payloadListCode words)
    (payloadListCode (denseContinuantReferenceRows n words).reverse) (by rw [hd,hi])

theorem dense_continuant_rows_word_code (dimension : List Bool) (words : List (List Bool))
    (hk : wordValue dimension ≤ (pair dimension (payloadListCode words)).length) :
    polynomialDenseContinuantRows (pair dimension (payloadListCode words))=
      payloadListCode (denseContinuantReferenceRows (wordValue dimension) words) := by
  obtain ⟨i,hi,he⟩ := row_projection_complete (pair dimension (payloadListCode words)).length
    (wordValue dimension) words (canonicalWord dimension) (canonical_word_value dimension) hk
  simp only [polynomialDenseContinuantRows,rowProjectionState,rowProjectionInitial,pairFst_pair,pairSnd_pair,he]
  simp only [rowProjectionPack,pairSnd_pair]
  rw [payload_reverse_code,List.reverse_reverse]

theorem dense_continuant_rows_square_code (n : ℕ) (words : List (List Bool))
    (hsize : words.length=n*n) :
    polynomialDenseContinuantRows (pair n.bits (payloadListCode words))=
      payloadListCode (denseContinuantReferenceRows n words) := by
  have hn : wordValue n.bits=n := by rw [word_value_foldr];exact IV04.Paper.bits_foldr n
  have hk : wordValue n.bits ≤ (pair n.bits (payloadListCode words)).length := by
    have h := payload_list_count_length words
    have hs : n ≤ n*n := by nlinarith
    rw [hn];simp only [pair_length];omega
  simpa only [hn] using dense_continuant_rows_word_code n.bits words hk

#print axioms dense_continuant_rows_square_code
end IV04.Paper.Computational