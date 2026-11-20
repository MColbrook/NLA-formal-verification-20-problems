module

public import NLA.IV04.PaperMatrixCoefficientInputSemantics
public import NLA.IV04.PaperRationalParserBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem read_rational_result_budget (input : List Bool) (q : ℚ) (tail : List Bool)
    (h : IV04.Paper.readRational input=some (q,tail)) : tail.length+3 ≤ input.length := by
  have he := rational_parser_exact input
  rw [h] at he
  by_cases hf : pairFst (encodedRationalParser input)=[true]
  · simp only [hf,if_true,Option.some.injEq,Prod.mk.injEq] at he
    have hb := rational_parser_success_budget input hf
    rw [he.2] at hb
    omega
  · simp [hf] at he

theorem read_rationals_input_budget (count : ℕ) (input : List Bool) (values : List ℚ) (tail : List Bool)
    (h : readRationals count input=some (values,tail)) : tail.length+3*count ≤ input.length := by
  induction count generalizing input values tail with
  | zero =>
    have he : []=values ∧ input=tail := by simpa only [readRationals,Option.some.injEq,Prod.mk.injEq] using h
    rw [←he.2]
    simp
  | succ count ih =>
    cases hn : IV04.Paper.readRational input with
    | none => simp [readRationals,hn] at h
    | some result =>
      obtain ⟨q,rest⟩ := result
      cases hr : readRationals count rest with
      | none => simp [readRationals,hn,hr] at h
      | some result =>
        obtain ⟨qs,last⟩ := result
        have he : q::qs=values ∧ last=tail := by simpa [readRationals,hn,hr] using h
        have hb := read_rational_result_budget input q rest hn
        have ht := ih rest qs last hr
        rw [he.2] at ht
        omega

theorem read_matrix_dimension_input_budget (input : List Bool) (n : ℕ) (values : List ℚ) (tail : List Bool)
    (h : readMatrixRationals input=some (n,values,tail)) : tail.length+6*n*n+4 ≤ input.length := by
  cases hn : IV04.Paper.readNatural input with
  | none => simp [readMatrixRationals,hn] at h
  | some result =>
    obtain ⟨dim,rest⟩ := result
    cases hr : readRationals (2*dim*dim+1) rest with
    | none => simp [readMatrixRationals,hn,hr] at h
    | some result =>
      obtain ⟨qs,last⟩ := result
      have he : dim=n ∧ qs=values ∧ last=tail := by simpa [readMatrixRationals,hn,hr] using h
      obtain ⟨rfl,rfl,rfl⟩ := he
      obtain ⟨payload,hp,hv⟩ := natural_parser_success_shape input dim rest hn
      have hf : pairFst (encodedNaturalParser input)=[true] := by rw [hp,pairFst_pair]
      have hh := natural_parser_success_budget input hf
      simp only [hp,pairFst_pair,pairSnd_pair] at hh
      have hb := read_rationals_input_budget (2*dim*dim+1) rest qs last hr
      nlinarith [hb,hh]

/-- A dense vertex uses one choice bit per entry; successful parsing bounds that
    count by the physical input length, even for malicious binary dimensions. -/
theorem matrix_vertex_certificate_bit_budget (input : List Bool) (n : ℕ) (values : List ℚ) (tail : List Bool)
    (h : readMatrixRationals input=some (n,values,tail)) : n*n ≤ input.length := by
  have hb := read_matrix_dimension_input_budget input n values tail h
  nlinarith [hb]

#print axioms matrix_vertex_certificate_bit_budget
end IV04.Paper.Computational
