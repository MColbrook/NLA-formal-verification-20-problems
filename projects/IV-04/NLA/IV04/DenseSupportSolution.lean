module

public import NLA.IV04.PaperDenseTridiagonalSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem verified_dense_support_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((denseSupportStep^[k]) (denseSupportInitial input)).length ≤ 6*input.length+11+9*k := by
  exact dense_support_initial_iterate_length k input

theorem verified_encoded_dense_tridiagonal_support_mem_fp : encodedDenseTridiagonalSupport ∈ FP := by
  exact encoded_dense_tridiagonal_support_mem_fp

theorem verified_dense_support_endpoint_step (d c i j lower upper rest : List Bool) (valid : Bool)
    (hc : wordValue c ≠ 0) :
    denseSupportStep (denseSupportPack d c i j (pair lower (pair upper rest)) [valid])=
      denseSupportPack d (decrementCount c)
        (if wordValue d ≤ wordValue j+1 then canonicalWord (polynomialWordAdd i [true]) else i)
        (if wordValue d ≤ wordValue j+1 then [] else canonicalWord (polynomialWordAdd j [true])) rest
        [valid && decide ((wordValue i ≤ wordValue j+1 ∧ wordValue j ≤ wordValue i+1) ∨
          (signedWordValue lower=0 ∧ signedWordValue upper=0))] := by
  exact dense_support_endpoint_step d c i j lower upper rest valid hc

theorem verified_dense_support_iterate_codes (rows : List (List Bool × List Bool))
    (k : ℕ) (d c i j rest : List Bool) (valid : Bool)
    (hc : wordValue c=rows.length) (hk : rows.length ≤ k) :
    ∃ c' i' j' : List Bool, wordValue c'=0 ∧
      (denseSupportStep^[k]) (denseSupportPack d c i j (endpointWordPairsCode rows rest) [valid])=
        denseSupportPack d c' i' j' rest
          [decide (valid=true ∧ denseEndpointAll (wordValue d) (wordValue i) (wordValue j) rows)] := by
  exact dense_support_iterate_codes rows k d c i j rest valid hc hk

theorem verified_dense_support_input_codes (n : ℕ) (rows : List (List Bool × List Bool)) (rest : List Bool)
    (hsize : rows.length=n*n) :
    encodedDenseTridiagonalSupport (denseSupportInputCode n rows rest)=
      pair [decide (denseEndpointAll n 0 0 rows)] rest := by
  exact dense_support_input_codes n rows rest hsize

#print axioms IV04.Paper.Computational.verified_dense_support_initial_iterate_length
#print axioms IV04.Paper.Computational.verified_encoded_dense_tridiagonal_support_mem_fp
#print axioms IV04.Paper.Computational.verified_dense_support_endpoint_step
#print axioms IV04.Paper.Computational.verified_dense_support_iterate_codes
#print axioms IV04.Paper.Computational.verified_dense_support_input_codes
end IV04.Paper.Computational
