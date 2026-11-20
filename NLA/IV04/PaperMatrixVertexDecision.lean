module

public import NLA.IV04.PaperMatrixVertexDecisionDefinitions
public import NLA.IV04.PaperMatrixVerifierCompleteValidation
public import NLA.IV04.PaperMatrixVerifierNP
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem rational_fields_pair_threshold_split (k : ℕ) (values : List ℚ) (hlen : values.length=2*k+1) :
    ∃ pairs : List (ℚ × ℚ), ∃ threshold : ℚ, pairs.length=k ∧
      values=pairs.flatMap (fun row => [row.1,row.2])++[threshold] := by
  induction k generalizing values with
  | zero =>
    cases values with
    | nil => simp at hlen
    | cons a values =>
      have he : values=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen;omega)
      subst values
      exact ⟨[],a,rfl,rfl⟩
  | succ k ih =>
    cases values with
    | nil => simp at hlen
    | cons a values =>
      cases values with
      | nil => simp only [List.length_cons,List.length_nil] at hlen;omega
      | cons b values =>
        have hl : values.length=2*k+1 := by simp only [List.length_cons] at hlen;omega
        obtain ⟨pairs,threshold,hsize,he⟩ := ih values hl
        refine ⟨(a,b)::pairs,threshold,by simpa using hsize,?_⟩
        rw [he]
        rfl

theorem matrix_rational_decode_pair_shape (matrix : List Bool) (n : ℕ) (values : List ℚ) (tail : List Bool)
    (hread : readMatrixRationals matrix=some (n,values,tail)) :
    ∃ pairs : List (ℚ × ℚ), ∃ threshold : ℚ, pairs.length=n*n ∧
      values=pairs.flatMap (fun row => [row.1,row.2])++[threshold] := by
  obtain ⟨_,_,coefficients,_,_,_,hvalues,hl⟩ := matrix_coefficient_input_correct matrix n values tail hread
  have he : coefficients.length=values.length := by
    have h := congrArg List.length hvalues;simpa only [List.length_map] using h
  have hv : values.length=2*(n*n)+1 := by simpa only [Nat.mul_assoc] using he.symm.trans hl
  exact rational_fields_pair_threshold_split (n*n) values hv

theorem matrix_singleton_decide_eq_true (P : Prop) [Decidable P] : ([decide P] : List Bool)=[true] ↔ P := by simp

theorem matrix_bounded_witness_all_rational_inputs (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) :
    matrixBoundedWitness matrix choices ↔ tail=[] ∧ choices.length=n*n ∧
      (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
      threshold ≤ (rationalEndpointVertex n pairs choices).det := by
  have hb := matrix_vertex_certificate_bit_budget matrix n _ tail hread
  have hout := matrix_determinant_verifier_all_rational_inputs matrix choices tail n pairs threshold hread hsize
  rw [matrixBoundedWitness,hout,matrix_singleton_decide_eq_true]
  constructor
  · exact And.right
  · intro h
    exact ⟨by rw [h.2.1];omega,h⟩

/-- Exact equality for all binary inputs, including malformed decodes, short/long certificates, and unordered endpoints. -/
theorem matrix_verifier_language_exact_vertex_language (matrix : List Bool) :
    matrix ∈ matrixVerifierLanguage ↔ matrix ∈ rationalMatrixVertexDecisionLanguage := by
  constructor
  · rintro ⟨choices,hc⟩
    cases hr : readMatrixRationals matrix with
    | none =>
      have h := hc.2
      rw [matrix_determinant_verifier_decode_failure matrix choices hr] at h
      contradiction
    | some result =>
      obtain ⟨n,values,tail⟩ := result
      obtain ⟨pairs,threshold,hsize,he⟩ := matrix_rational_decode_pair_shape matrix n values tail hr
      rw [he] at hr
      have h := (matrix_bounded_witness_all_rational_inputs matrix choices tail n pairs threshold hr hsize).mp hc
      rw [h.1] at hr
      exact ⟨n,pairs,threshold,hr,hsize,h.2.2.1,h.2.2.2.1,choices,h.2.1,h.2.2.2.2⟩
  · rintro ⟨n,pairs,threshold,hr,hsize,ho,hsupport,choices,hlen,hdet⟩
    exact ⟨choices,(matrix_bounded_witness_all_rational_inputs matrix choices [] n pairs threshold hr hsize).mpr
      ⟨rfl,hlen,ho,hsupport,hdet⟩⟩

theorem rational_matrix_vertex_decision_language_mem_np : rationalMatrixVertexDecisionLanguage ∈ NP := by
  have he : rationalMatrixVertexDecisionLanguage=matrixVerifierLanguage :=
    Set.ext (fun matrix => (matrix_verifier_language_exact_vertex_language matrix).symm)
  rw [he]
  exact matrix_verifier_language_mem_np

#print axioms rational_matrix_vertex_decision_language_mem_np
end IV04.Paper.Computational