module

public import NLA.IV04.PaperPayloadLookupDefinitions
public import NLA.IV04.PaperCountedMachineStep
public import NLA.IV04.PaperWordListProductBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem payload_lookup_step_pair (count fields : List Bool) :
    payloadLookupStep (pair count fields)=
      caseBit₀ (nonemptyFlag (canonicalWord count))
        (pair (decrementCount count) (pairSnd fields)) (pair count fields) := by
  simp only [payloadLookupStep,pairFst_pair,pairSnd_pair]

theorem payload_lookup_step_shape (count fields : List Bool) :
    ∃ c f : List Bool, payloadLookupStep (pair count fields)=pair c f ∧
      c.length ≤ count.length ∧ f.length ≤ fields.length := by
  rw [payload_lookup_step_pair]
  apply case_bit_zero_property (P:=fun result => ∃ c f : List Bool,
    result=pair c f ∧ c.length ≤ count.length ∧ f.length ≤ fields.length)
  · refine ⟨_,_,rfl,decrement_count_length count,?_⟩
    have h := pair_projection_budget fields;omega
  · exact ⟨count,fields,rfl,le_rfl,le_rfl⟩

theorem payload_lookup_iterate_shape (k : ℕ) (count fields : List Bool) :
    ∃ c f : List Bool, (payloadLookupStep^[k]) (pair count fields)=pair c f ∧
      c.length ≤ count.length ∧ f.length ≤ fields.length := by
  induction k with
  | zero => exact ⟨count,fields,rfl,le_rfl,le_rfl⟩
  | succ k ih =>
    obtain ⟨c,f,he,hc,hf⟩ := ih
    obtain ⟨c',f',hs,hc',hf'⟩ := payload_lookup_step_shape c f
    exact ⟨c',f',by rw [Function.iterate_succ_apply',he,hs],hc'.trans hc,hf'.trans hf⟩

theorem payload_lookup_iterate_length (k : ℕ) (input : List Bool) :
    ((payloadLookupStep^[k]) (pair (pairFst input) (pairSnd input))).length ≤ 2*input.length+2 := by
  obtain ⟨c,f,he,hc,hf⟩ := payload_lookup_iterate_shape k (pairFst input) (pairSnd input)
  have h := pair_projection_budget input
  rw [he,pair_length];omega

theorem polynomial_payload_lookup_length (input : List Bool) :
    (polynomialPayloadLookup input).length ≤ (pairSnd input).length := by
  obtain ⟨c,f,he,hc,hf⟩ := payload_lookup_iterate_shape input.length (pairFst input) (pairSnd input)
  simp only [polynomialPayloadLookup,payloadLookupState,he,pairSnd_pair]
  have h := pair_projection_budget f;omega

#print axioms payload_lookup_iterate_length
end IV04.Paper.Computational
