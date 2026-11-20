module

public import NLA.IV04.PaperFullHullProjectionDefinitions
public import NLA.IV04.PaperExactOutputHardness
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem polynomial_first_hull_projection_mem_fp : polynomialFirstHullProjection ∈ FP := by
  exact CobhamFP_subset_FP ((Cobham.comp polynomial_fraction_output_cobham
    (fun _ : Fin 1 => rational_parser_fraction_cobham)).of_eq (fun _ => rfl))

theorem exact_full_hull_output_projects (matrix answer : List Bool)
    (h : ExactFullHullOutput matrix answer) :
    ExactFirstHullEndpointOutput matrix (polynomialFirstHullProjection answer) := by
  obtain ⟨n,hn,pairs,bounds,hr,hlen,horder,hsupport,hregular,hne,hbounded,hblen,hanswer,hcoords⟩ := h
  cases bounds with
  | nil => simp only [List.length_nil] at hblen;omega
  | cons row rows =>
    have hread : IV04.Paper.readRational answer =
        some (row.1,IV04.Paper.rationalCode row.2 ++
          rows.flatMap (fun other => IV04.Paper.rationalCode other.1 ++ IV04.Paper.rationalCode other.2)) := by
      rw [hanswer,List.flatMap_cons,List.append_assoc]
      exact IV04.Paper.read_rational_code row.1 _
    have hv := (rational_parser_success_value_tail answer row.1 _ hread).1
    have hmin := (hcoords ⟨0,hn⟩).1
    change IsLeast (IV04.Paper.positiveFirstCoordinates n hn (realDenseIntervalBox n pairs)) (row.1 : ℝ) at hmin
    refine ⟨n,hn,pairs,hr,hlen,horder,hsupport,hregular,hne,hbounded,row.1,?_,hmin⟩
    have hp := polynomial_fraction_output_read (rationalParserFraction answer) []
    simpa only [List.append_nil,polynomialFirstHullProjection,hv] using hp

theorem complete_hull_output_contains_np_hard_endpoint :
    NPHardOutputTask ExactFirstHullEndpointOutput ∧
      polynomialFirstHullProjection ∈ FP ∧
      ∀ matrix answer, ExactFullHullOutput matrix answer →
        ExactFirstHullEndpointOutput matrix (polynomialFirstHullProjection answer) :=
  ⟨exact_first_hull_endpoint_output_np_hard,polynomial_first_hull_projection_mem_fp,
    exact_full_hull_output_projects⟩

#print axioms polynomial_first_hull_projection_mem_fp
#print axioms exact_full_hull_output_projects
#print axioms complete_hull_output_contains_np_hard_endpoint
end IV04.Paper.Computational
