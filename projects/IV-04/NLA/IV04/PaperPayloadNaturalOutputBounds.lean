module

public import NLA.IV04.PaperPayloadNaturalOutputDefinitions
public import NLA.IV04.PaperCanonicalWord
public import NLA.IV04.PaperWordListProductBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem payload_natural_output_step_pair (rest output : List Bool) :
    payloadNaturalOutputStep (Complexity.pair rest output) =
      if rest=[] then Complexity.pair rest output else
        Complexity.pair (Complexity.pairSnd rest)
          (output ++ canonicalWordCode (Complexity.pairFst rest)) := by
  simp only [payloadNaturalOutputStep,Complexity.pairFst_pair,Complexity.pairSnd_pair]
  cases rest <;> simp [Complexity.nonemptyFlag,Complexity.caseBit,Complexity.caseBit₀]

theorem payload_natural_output_step_shape (rest output : List Bool) :
    ∃ r o : List Bool, payloadNaturalOutputStep (Complexity.pair rest output)=Complexity.pair r o ∧
      (Complexity.pair r o).length ≤ (Complexity.pair rest output).length+1 := by
  rw [payload_natural_output_step_pair]
  split_ifs with he
  · exact ⟨rest,output,rfl,Nat.le_succ _⟩
  · refine ⟨_,_,rfl,?_⟩
    have hp := pair_projection_budget rest
    have hc := canonical_word_code_length_bound (Complexity.pairFst rest)
    simp only [Complexity.pair_length,List.length_append]
    omega

theorem payload_natural_output_iterate_shape (k : ℕ) (rest output : List Bool) :
    ∃ r o : List Bool,
      (payloadNaturalOutputStep^[k]) (Complexity.pair rest output)=Complexity.pair r o ∧
      (Complexity.pair r o).length ≤ (Complexity.pair rest output).length+k := by
  induction k with
  | zero => exact ⟨rest,output,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨r,o,he,hl⟩ := ih
    obtain ⟨r',o',hs,hbound⟩ := payload_natural_output_step_shape r o
    refine ⟨r',o',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

theorem payload_natural_output_iterate_length (k : ℕ) (rest output : List Bool) :
    ((payloadNaturalOutputStep^[k]) (Complexity.pair rest output)).length ≤
      2*rest.length+output.length+2+k := by
  obtain ⟨r,o,he,hl⟩ := payload_natural_output_iterate_shape k rest output
  rw [he]
  simp only [Complexity.pair_length] at hl ⊢
  omega

#print axioms payload_natural_output_iterate_length
end IV04.Paper.Computational
