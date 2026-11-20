module

public import NLA.IV04.PaperPayloadLookupPoly
public import NLA.IV04.PaperWordListProductSemantics
public import NLA.IV04.PaperVertexSelectionStep
public import NLA.IV04.PaperEncoding
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem payload_lookup_finished_iterate (k : ℕ) (count fields : List Bool) (h : wordValue count=0) :
    (payloadLookupStep^[k]) (pair count fields)=pair count fields := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,payload_lookup_step_pair,canonical_nonempty_flag]
    simp [h,caseBit₀]

theorem payload_lookup_iterate_code (r k : ℕ) (count : List Bool) (rows : List (List Bool))
    (hv : wordValue count=r) (hr : r ≤ rows.length) (hk : r ≤ k) :
    ∃ c : List Bool, wordValue c=0 ∧
      (payloadLookupStep^[k]) (pair count (payloadListCode rows))=pair c (payloadListCode (rows.drop r)) := by
  induction r generalizing k count rows with
  | zero => exact ⟨count,hv,by simpa using payload_lookup_finished_iterate k count (payloadListCode rows) hv⟩
  | succ r ih =>
    cases rows with
    | nil => simp at hr
    | cons row rows =>
      cases k with
      | zero => omega
      | succ k =>
        have hcount : wordValue count ≠ 0 := by omega
        have hd : wordValue (decrementCount count)=r := by rw [decrement_count_value,hv];omega
        have hr' : r ≤ rows.length := by simp only [List.length_cons] at hr;omega
        have hk' : r ≤ k := by omega
        obtain ⟨c,hc,he⟩ := ih k (decrementCount count) rows hd hr' hk'
        refine ⟨c,hc,?_⟩
        rw [Function.iterate_succ_apply,payload_lookup_step_pair,canonical_nonempty_flag]
        simp only [hcount,if_false,payloadListCode,pairSnd_pair]
        simp [caseBit₀,he]

theorem payload_lookup_code (rows : List (List Bool)) (r : ℕ) (hr : r < rows.length) :
    polynomialPayloadLookup (pair r.bits (payloadListCode rows))=rows[r] := by
  have hv : wordValue r.bits=r := by rw [word_value_foldr];exact IV04.Paper.bits_foldr r
  have hk : r ≤ (pair r.bits (payloadListCode rows)).length := by
    have h := payload_list_count_length rows
    simp only [pair_length];omega
  obtain ⟨c,hc,he⟩ := payload_lookup_iterate_code r (pair r.bits (payloadListCode rows)).length
    r.bits rows hv (Nat.le_of_lt hr) hk
  simp only [polynomialPayloadLookup,payloadLookupState,pairFst_pair,pairSnd_pair,he]
  have heq : rows.drop r=rows[r]::rows.drop (r+1) := List.drop_eq_getElem_cons hr
  rw [heq]
  simp [payloadListCode,pairFst_pair]

theorem payload_lookup_word_code (rows : List (List Bool)) (index : List Bool)
    (hr : wordValue index < rows.length) :
    polynomialPayloadLookup (pair index (payloadListCode rows))=rows[wordValue index] := by
  have hk : wordValue index ≤ (pair index (payloadListCode rows)).length := by
    have h := payload_list_count_length rows
    simp only [pair_length];omega
  obtain ⟨c,hc,he⟩ := payload_lookup_iterate_code (wordValue index)
    (pair index (payloadListCode rows)).length index rows rfl (Nat.le_of_lt hr) hk
  simp only [polynomialPayloadLookup,payloadLookupState,pairFst_pair,pairSnd_pair,he]
  have heq : rows.drop (wordValue index)=rows[wordValue index]::rows.drop (wordValue index+1) :=
    List.drop_eq_getElem_cons hr
  rw [heq]
  simp [payloadListCode,pairFst_pair]

theorem payload_lookup_iterate_past_end (rows : List (List Bool)) (k : ℕ) (count : List Bool)
    (hv : rows.length ≤ wordValue count) (hk : rows.length ≤ k) :
    ∃ c : List Bool, (payloadLookupStep^[k]) (pair count (payloadListCode rows))=pair c [] := by
  induction rows generalizing k count with
  | nil =>
    obtain ⟨c,f,he,hc,hf⟩ := payload_lookup_iterate_shape k count []
    have hz : f=[] := by simpa using hf
    subst f
    exact ⟨c,he⟩
  | cons row rows ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      have hcount : wordValue count ≠ 0 := by simp only [List.length_cons] at hv;omega
      have hd : rows.length ≤ wordValue (decrementCount count) := by
        rw [decrement_count_value];simp only [List.length_cons] at hv;omega
      have hk' : rows.length ≤ k := by simp only [List.length_cons] at hk;omega
      obtain ⟨c,he⟩ := ih k (decrementCount count) hd hk'
      refine ⟨c,?_⟩
      rw [Function.iterate_succ_apply,payload_lookup_step_pair,canonical_nonempty_flag]
      simp only [hcount,if_false,payloadListCode,pairSnd_pair]
      simp [caseBit₀,he]

theorem payload_lookup_word_past_end (rows : List (List Bool)) (index : List Bool)
    (hr : rows.length ≤ wordValue index) :
    polynomialPayloadLookup (pair index (payloadListCode rows))=[] := by
  have hk : rows.length ≤ (pair index (payloadListCode rows)).length := by
    have h := payload_list_count_length rows
    simp only [pair_length];omega
  obtain ⟨c,he⟩ := payload_lookup_iterate_past_end rows (pair index (payloadListCode rows)).length index hr hk
  simp only [polynomialPayloadLookup,payloadLookupState,pairFst_pair,pairSnd_pair,he]
  rfl

#print axioms payload_lookup_word_code
#print axioms payload_lookup_word_past_end

#print axioms payload_lookup_code
end IV04.Paper.Computational
