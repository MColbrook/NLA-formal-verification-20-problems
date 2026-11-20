module

public import NLA.IV04.FullHullHardnessProof
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04FullHullHardness
open Complexity IV04.Paper.Computational
open IV04.Paper.Computational.SATReduction

theorem project_full_hull_packet_mem_fp : projectFullHullPacket ∈ FP := by
  exact Reference.IV04FullHullHardnessProof.project_full_hull_packet_mem_fp

theorem sat_full_hull_finish_mem_fp : satFullHullFinish ∈ FP := by
  exact Reference.IV04FullHullHardnessProof.sat_full_hull_finish_mem_fp

theorem sat_full_hull_output_exists (input : List Bool) :
    ∃ answer, ExactFullHullOutput (polynomialSATOutputQuery input) answer := by
  exact Reference.IV04FullHullHardnessProof.sat_full_hull_output_exists input

theorem sat_full_hull_finish_correct (input answer : List Bool)
    (h : ExactFullHullOutput (polynomialSATOutputQuery input) answer) :
    firstBit (satFullHullFinish (pair input answer)) = true ↔ input ∈ SAT.language := by
  exact Reference.IV04FullHullHardnessProof.sat_full_hull_finish_correct input answer h

theorem sat_full_hull_one_query_reduction :
    PolynomialOneQueryReduction SAT.language ExactFullHullOutput := by
  exact Reference.IV04FullHullHardnessProof.sat_full_hull_one_query_reduction

theorem iv_hull_literal_np_hard : NPHardOutputTask ExactFullHullOutput := by
  exact Reference.IV04FullHullHardnessProof.iv_hull_literal_np_hard

#print axioms project_full_hull_packet_mem_fp
#print axioms sat_full_hull_finish_mem_fp
#print axioms sat_full_hull_output_exists
#print axioms sat_full_hull_finish_correct
#print axioms sat_full_hull_one_query_reduction
#print axioms iv_hull_literal_np_hard
end Reference.IV04FullHullHardness
