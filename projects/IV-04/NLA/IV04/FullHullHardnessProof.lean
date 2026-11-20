module

public import NLA.IV04.FullHullHardnessDefinitions
public import NLA.IV04.PaperFullHullProjection
public import NLA.IV04.RationalBoxExtrema.FullHullOutput
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04FullHullHardnessProof
open Complexity IV04.Paper.Computational
open IV04.Paper.Computational.SATReduction
open Reference.IV04FullHullHardness

theorem project_full_hull_packet_mem_fp : projectFullHullPacket ∈ FP := by
  have hp := FP_subset_CobhamFP polynomial_first_hull_projection_mem_fp
  exact CobhamFP_subset_FP ((Cobham.comp₂ Cobham.pairing
    (Cobham.fstBlockFn (.proj (0 : Fin 1)))
    ((Cobham.comp hp (fun _ : Fin 1 => Cobham.sndBlockFn (.proj (0 : Fin 1)))).of_eq
      (fun _ => rfl))).of_eq (fun _ => rfl))

theorem sat_full_hull_finish_mem_fp : satFullHullFinish ∈ FP := by
  have heq : satFullHullFinish = polynomialSATHullAnswer ∘ projectFullHullPacket := by
    funext input
    simp only [satFullHullFinish,Function.comp_apply]
  rw [heq]
  exact mem_FP_comp project_full_hull_packet_mem_fp polynomial_sat_hull_answer_mem_fp

theorem sat_full_hull_output_exists (input : List Bool) :
    ∃ answer, ExactFullHullOutput (polynomialSATOutputQuery input) answer := by
  obtain ⟨P,hP⟩ := polynomial_sat_partition_output_canonical input
  simpa only [polynomialSATOutputQuery,hP] using
    Reference.IV04RationalBoxExtrema.partition_exact_full_hull_output_exists P

theorem sat_full_hull_finish_correct (input answer : List Bool)
    (h : ExactFullHullOutput (polynomialSATOutputQuery input) answer) :
    firstBit (satFullHullFinish (pair input answer)) = true ↔ input ∈ SAT.language := by
  have hp := exact_full_hull_output_projects (polynomialSATOutputQuery input) answer h
  simpa only [satFullHullFinish,projectFullHullPacket,pairFst_pair,pairSnd_pair] using
    polynomial_sat_first_hull_answer_correct input (polynomialFirstHullProjection answer) hp

theorem sat_full_hull_one_query_reduction :
    PolynomialOneQueryReduction SAT.language ExactFullHullOutput := by
  exact ⟨polynomialSATOutputQuery,polynomial_sat_output_query_mem_fp,
    satFullHullFinish,sat_full_hull_finish_mem_fp,sat_full_hull_output_exists,
    sat_full_hull_finish_correct⟩

theorem iv_hull_literal_np_hard : NPHardOutputTask ExactFullHullOutput := by
  intro L hL
  exact one_query_reduction_of_map (actual_binary_sat_np_complete.2 L hL)
    sat_full_hull_one_query_reduction

#print axioms project_full_hull_packet_mem_fp
#print axioms sat_full_hull_finish_mem_fp
#print axioms sat_full_hull_output_exists
#print axioms sat_full_hull_finish_correct
#print axioms sat_full_hull_one_query_reduction
#print axioms iv_hull_literal_np_hard
end Reference.IV04FullHullHardnessProof
