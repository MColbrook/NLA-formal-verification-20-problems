module

public import NLA.IV04.PaperSubsetPartitionBuilderDefinitions
public import NLA.IV04.PaperPayloadNaturalOutputPoly
public import NLA.IV04.PaperWordListSumPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem subset_partition_builder_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSubsetPartitionCode (v 0) := by
  have hc := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have ht := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hw := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hs := Cobham.comp (Cobham.sndBlockFn word_list_sum_state_cobham) fun _ : Fin 1 => hw
  have hfirst := Cobham.comp₂ polynomial_word_add_cobham hs
    (Cobham.comp₂ polynomial_word_add_cobham (Cobham.comp₂ polynomial_word_add_cobham ht ht) (.const [true]))
  have hsecond := Cobham.comp₂ polynomial_word_add_cobham
    (Cobham.comp₂ polynomial_word_add_cobham hs hs) (.const [true])
  have hcount := Cobham.comp₂ polynomial_word_add_cobham hc (.const [false,true])
  have hout := Cobham.comp (Cobham.sndBlockFn payload_natural_output_state_cobham) fun _ : Fin 1 => hw
  have hcc := Cobham.comp canonical_word_code_cobham fun _ : Fin 1 => hcount
  have hfc := Cobham.comp canonical_word_code_cobham fun _ : Fin 1 => hfirst
  have hsc := Cobham.comp canonical_word_code_cobham fun _ : Fin 1 => hsecond
  exact (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn hcc hout) hfc) hsc).of_eq fun _ => rfl

theorem polynomial_subset_partition_code_mem_fp : polynomialSubsetPartitionCode ∈ FP :=
  CobhamFP_subset_FP subset_partition_builder_cobham

#print axioms polynomial_subset_partition_code_mem_fp
end IV04.Paper.Computational
