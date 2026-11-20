module

public import NLA.IV04.PaperDenseContinuantProjectionDefinitions
public import NLA.IV04.PaperPayloadLookupBounds
public import NLA.IV04.PaperDenseTridiagonalBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem row_projection_pack_length (d i f o : List Bool) :
    (rowProjectionPack d i f o).length=2*d.length+2*i.length+2*f.length+o.length+6 := by
  simp [rowProjectionPack,pair_length];omega

theorem row_projection_row_length (d i f : List Bool) :
    (rowProjectionRow d i f).length ≤ 5*f.length+7 := by
  have hd := polynomial_payload_lookup_length (pair (rowProjectionDiagonalIndex d i) f)
  have hl := polynomial_payload_lookup_length (pair (rowProjectionLowerIndex d i) f)
  have hu := polynomial_payload_lookup_length (pair (rowProjectionPreviousUpperIndex d i) f)
  simp only [pairSnd_pair] at hd hl hu
  have hl' := case_bit_zero_property (P:=fun bits => bits.length ≤ f.length+1)
    (nonemptyFlag (canonicalWord i)) (polynomialPayloadLookup (pair (rowProjectionLowerIndex d i) f))
    [false] (by omega) (by simp)
  have hu' := case_bit_zero_property (P:=fun bits => bits.length ≤ f.length+1)
    (nonemptyFlag (canonicalWord i)) (polynomialPayloadLookup (pair (rowProjectionPreviousUpperIndex d i) f))
    [false] (by omega) (by simp)
  simp only [rowProjectionRow,integerContinuantRow,pair_length]
  omega

theorem row_projection_step_pack (d i f o : List Bool) :
    rowProjectionStep (rowProjectionPack d i f o)=
      caseBit₀ (polynomialWordLe d i) (rowProjectionPack d i f o)
        (rowProjectionPack d (canonicalWord (polynomialWordAdd i [true])) f
          (pair (rowProjectionRow d i f) o)) := by
  simp only [rowProjectionStep,rowProjectionPack,pairFst_pair,pairSnd_pair]

theorem row_projection_step_shape (d i f o : List Bool) :
    ∃ i' o' : List Bool, rowProjectionStep (rowProjectionPack d i f o)=rowProjectionPack d i' f o' ∧
      i'.length ≤ i.length+2 ∧ o'.length ≤ o.length+10*f.length+16 := by
  rw [row_projection_step_pack]
  apply case_bit_zero_property (P:=fun result => ∃ i' o' : List Bool,
    result=rowProjectionPack d i' f o' ∧ i'.length ≤ i.length+2 ∧
      o'.length ≤ o.length+10*f.length+16)
  · exact ⟨i,o,rfl,by omega,by omega⟩
  · refine ⟨_,_,rfl,dense_increment_word_length i,?_⟩
    have h := row_projection_row_length d i f
    rw [pair_length];omega

theorem row_projection_iterate_shape (k : ℕ) (d i f o : List Bool) :
    ∃ i' o' : List Bool, (rowProjectionStep^[k]) (rowProjectionPack d i f o)=rowProjectionPack d i' f o' ∧
      i'.length ≤ i.length+2*k ∧ o'.length ≤ o.length+(10*f.length+16)*k := by
  induction k with
  | zero => exact ⟨i,o,rfl,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨i',o',he,hi,ho⟩ := ih
    obtain ⟨i'',o'',hs,hi',ho'⟩ := row_projection_step_shape d i' f o'
    refine ⟨i'',o'',by rw [Function.iterate_succ_apply',he,hs],?_,?_⟩
    · omega
    · rw [Nat.mul_succ];omega

theorem row_projection_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((rowProjectionStep^[k]) (rowProjectionInitial input)).length ≤
      2*input.length+6+(10*input.length+20)*k := by
  obtain ⟨i,o,he,hi,ho⟩ := row_projection_iterate_shape k
    (canonicalWord (pairFst input)) [] (pairSnd input) []
  have hd := canonical_word_length (pairFst input)
  have hp := pair_projection_budget input
  have hf : (pairSnd input).length ≤ input.length := by omega
  have hprod := Nat.mul_le_mul_right k (show 10*(pairSnd input).length+16 ≤ 10*input.length+16 by omega)
  change ((rowProjectionStep^[k]) (rowProjectionPack (canonicalWord (pairFst input)) [] (pairSnd input) [])).length ≤ _
  rw [he,row_projection_pack_length]
  simp only [List.length_nil,Nat.zero_add] at hi ho
  have harith : (10*input.length+20)*k=(10*input.length+16)*k+4*k := by ring
  rw [harith]
  omega

#print axioms row_projection_initial_iterate_length
end IV04.Paper.Computational
