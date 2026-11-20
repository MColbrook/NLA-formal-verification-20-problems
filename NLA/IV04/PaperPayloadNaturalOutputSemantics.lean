module

public import NLA.IV04.PaperPayloadNaturalOutputPoly
public import NLA.IV04.PaperCanonicalWordBridge
public import NLA.IV04.PaperWordListProductSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem payload_natural_output_iterate_nil (k : ℕ) (output : List Bool) :
    (payloadNaturalOutputStep^[k]) (Complexity.pair [] output)=Complexity.pair [] output := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,payload_natural_output_step_pair]; simp

theorem payload_natural_output_iteration (k : ℕ) (payloads : List (List Bool)) (output : List Bool)
    (h : payloads.length ≤ k) :
    (payloadNaturalOutputStep^[k]) (Complexity.pair (payloadListCode payloads) output)=
      Complexity.pair [] (output ++ payloads.flatMap (fun w => IV04.Paper.naturalCode (wordValue w))) := by
  induction k generalizing payloads output with
  | zero =>
    have he : payloads=[] := by cases payloads <;> simp_all
    simp [he,payloadListCode]
  | succ k ih =>
    cases payloads with
    | nil => simp [payloadListCode,payload_natural_output_iterate_nil]
    | cons payload payloads =>
      have ht : payloads.length ≤ k := by simp only [List.length_cons] at h; omega
      have hn : Complexity.pair payload (payloadListCode payloads) ≠ [] := by
        intro he
        have hl := congrArg List.length he
        simp only [Complexity.pair_length,List.length_nil] at hl
        omega
      rw [Function.iterate_succ_apply,payload_natural_output_step_pair]
      simp only [payloadListCode,hn,if_false,Complexity.pairFst_pair,Complexity.pairSnd_pair]
      rw [ih payloads (output ++ canonicalWordCode payload) ht,canonical_word_code_exact]
      simp only [List.flatMap_cons,List.append_assoc]

theorem polynomial_payload_naturals_exact (payloads : List (List Bool)) :
    polynomialPayloadNaturals (payloadListCode payloads)=
      payloads.flatMap (fun w => IV04.Paper.naturalCode (wordValue w)) := by
  have h := payload_natural_output_iteration (payloadListCode payloads).length payloads []
    (payload_list_count_length payloads)
  simpa [polynomialPayloadNaturals,payloadNaturalOutputState] using congrArg Complexity.pairSnd h

theorem payload_natural_output_actual_polytime : polynomialPayloadNaturals ∈ Complexity.FP ∧
    ∀ payloads, polynomialPayloadNaturals (payloadListCode payloads)=
      payloads.flatMap (fun w => IV04.Paper.naturalCode (wordValue w)) :=
  ⟨polynomial_payload_naturals_mem_fp,polynomial_payload_naturals_exact⟩

#print axioms payload_natural_output_actual_polytime
end IV04.Paper.Computational
