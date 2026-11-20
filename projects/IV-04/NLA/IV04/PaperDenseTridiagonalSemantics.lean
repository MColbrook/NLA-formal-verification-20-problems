module

public import NLA.IV04.PaperDenseTridiagonalPoly
public import NLA.IV04.PaperDenseTridiagonalReference
public import NLA.IV04.PaperEncoding
public import NLA.IV04.PaperVertexSelectionStep
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem dense_support_finished_step (d c i j f b : List Bool) (h : wordValue c=0) :
    denseSupportStep (denseSupportPack d c i j f b)=denseSupportPack d c i j f b := by
  rw [dense_support_step_pack]
  unfold denseSupportTransition
  rw [canonical_nonempty_flag]
  simp [h,caseBit₀]

theorem dense_support_finished_iterate (k : ℕ) (d c i j f b : List Bool) (h : wordValue c=0) :
    (denseSupportStep^[k]) (denseSupportPack d c i j f b)=denseSupportPack d c i j f b := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,dense_support_finished_step d c i j f b h]

theorem dense_support_endpoint_step (d c i j lower upper rest : List Bool) (valid : Bool)
    (hc : wordValue c ≠ 0) :
    denseSupportStep (denseSupportPack d c i j (pair lower (pair upper rest)) [valid])=
      denseSupportPack d (decrementCount c)
        (if wordValue d ≤ wordValue j+1 then canonicalWord (polynomialWordAdd i [true]) else i)
        (if wordValue d ≤ wordValue j+1 then [] else canonicalWord (polynomialWordAdd j [true])) rest
        [valid && decide ((wordValue i ≤ wordValue j+1 ∧ wordValue j ≤ wordValue i+1) ∨
          (signedWordValue lower=0 ∧ signedWordValue upper=0))] := by
  rw [dense_support_step_pack]
  unfold denseSupportTransition
  rw [canonical_nonempty_flag]
  simp only [pairFst_pair,pairSnd_pair,vertex_selection_pair_nonempty_flag]
  rw [tridiagonal_endpoint_flag_value,polynomial_word_le_value,canonical_word_value,
    polynomial_word_add_value]
  have h1 : wordValue [true]=1 := rfl
  rw [h1]
  generalize decide ((wordValue i ≤ wordValue j+1 ∧ wordValue j ≤ wordValue i+1) ∨
    (signedWordValue lower=0 ∧ signedWordValue upper=0))=flag
  cases flag <;> by_cases hend : wordValue d ≤ wordValue j+1 <;>
    cases valid <;> simp [hc,hend,caseBit₀,andBit]

theorem dense_support_iterate_codes (rows : List (List Bool × List Bool))
    (k : ℕ) (d c i j rest : List Bool) (valid : Bool)
    (hc : wordValue c=rows.length) (hk : rows.length ≤ k) :
    ∃ c' i' j' : List Bool, wordValue c'=0 ∧
      (denseSupportStep^[k]) (denseSupportPack d c i j (endpointWordPairsCode rows rest) [valid])=
        denseSupportPack d c' i' j' rest
          [decide (valid=true ∧ denseEndpointAll (wordValue d) (wordValue i) (wordValue j) rows)] := by
  induction rows generalizing k c i j valid with
  | nil =>
    refine ⟨c,i,j,hc,?_⟩
    simpa [endpointWordPairsCode,denseEndpointAll] using
      dense_support_finished_iterate k d c i j rest [valid] hc
  | cons row rows ih =>
    obtain ⟨lower,upper⟩ := row
    cases k with
    | zero => simp at hk
    | succ k =>
      have hcount : wordValue c ≠ 0 := by simp only [List.length_cons] at hc;omega
      have hdec : wordValue (decrementCount c)=rows.length := by
        rw [decrement_count_value,hc,List.length_cons];omega
      have hclock : rows.length ≤ k := by simp only [List.length_cons] at hk;omega
      let nextRow := if wordValue d ≤ wordValue j+1 then canonicalWord (polynomialWordAdd i [true]) else i
      let nextCol := if wordValue d ≤ wordValue j+1 then [] else canonicalWord (polynomialWordAdd j [true])
      let p := (wordValue i ≤ wordValue j+1 ∧ wordValue j ≤ wordValue i+1) ∨
        (signedWordValue lower=0 ∧ signedWordValue upper=0)
      have hr : wordValue nextRow=if wordValue d ≤ wordValue j+1 then wordValue i+1 else wordValue i := by
        dsimp [nextRow];split <;> simp [canonical_word_value,polynomial_word_add_value,wordValue,bitValue]
      have hj : wordValue nextCol=if wordValue d ≤ wordValue j+1 then 0 else wordValue j+1 := by
        dsimp [nextCol];split <;> simp [canonical_word_value,polynomial_word_add_value,wordValue,bitValue]
      obtain ⟨c',i',j',hz,he⟩ := ih k (decrementCount c) nextRow nextCol (valid && decide p) hdec hclock
      refine ⟨c',i',j',hz,?_⟩
      rw [Function.iterate_succ_apply]
      simp only [endpointWordPairsCode]
      rw [dense_support_endpoint_step d c i j lower upper (endpointWordPairsCode rows rest) valid hcount]
      change (denseSupportStep^[k]) (denseSupportPack d (decrementCount c) nextRow nextCol
        (endpointWordPairsCode rows rest) [valid && decide p])=_
      rw [he,hr,hj]
      apply congrArg (denseSupportPack d c' i' j' rest)
      apply congrArg (fun bit : Bool => [bit])
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,Bool.and_eq_true]
      change ((valid=true ∧ p) ∧ denseEndpointAll (wordValue d)
        (if wordValue d ≤ wordValue j+1 then wordValue i+1 else wordValue i)
        (if wordValue d ≤ wordValue j+1 then 0 else wordValue j+1) rows) ↔
        (valid=true ∧ p ∧ denseEndpointAll (wordValue d)
        (if wordValue d ≤ wordValue j+1 then wordValue i+1 else wordValue i)
        (if wordValue d ≤ wordValue j+1 then 0 else wordValue j+1) rows)
      exact and_assoc

theorem dense_endpoint_code_length (rows : List (List Bool × List Bool)) (rest : List Bool) :
    rows.length ≤ (endpointWordPairsCode rows rest).length := by
  induction rows with
  | nil => simp
  | cons row rows ih => obtain ⟨lower,upper⟩ := row;simp only [endpointWordPairsCode,pair_length,List.length_cons];omega

theorem dense_support_input_codes (n : ℕ) (rows : List (List Bool × List Bool)) (rest : List Bool)
    (hsize : rows.length=n*n) :
    encodedDenseTridiagonalSupport (denseSupportInputCode n rows rest)=
      pair [decide (denseEndpointAll n 0 0 rows)] rest := by
  have hn : wordValue (canonicalWord n.bits)=n := by
    rw [canonical_word_value,word_value_foldr];exact IV04.Paper.bits_foldr n
  have hc : wordValue (canonicalWordMultiply (canonicalWord n.bits) (canonicalWord n.bits))=rows.length := by
    rw [canonical_word_multiply_value,hn];exact hsize.symm
  have hk : rows.length ≤ (denseSupportInputCode n rows rest).length := by
    have h := dense_endpoint_code_length rows rest
    simp only [denseSupportInputCode,pair_length];omega
  obtain ⟨c,i,j,hz,he⟩ := dense_support_iterate_codes rows
    (denseSupportInputCode n rows rest).length (canonicalWord n.bits)
    (canonicalWordMultiply (canonicalWord n.bits) (canonicalWord n.bits)) [] [] rest true hc hk
  have hs : denseSupportState (denseSupportInputCode n rows rest)=
      denseSupportPack (canonicalWord n.bits) c i j rest [decide (denseEndpointAll n 0 0 rows)] := by
    simpa only [denseSupportState,denseSupportInitial,denseSupportInputCode,pairFst_pair,pairSnd_pair,
      hn,wordValue,List.foldr_nil,eq_self_iff_true,true_and] using he
  rw [encodedDenseTridiagonalSupport,hs]
  simp only [denseSupportCount,denseSupportFlag,denseSupportFields,denseSupportPack,pairFst_pair,pairSnd_pair]
  rw [canonical_nonempty_flag]
  simp [hz,caseBit₀]

#print axioms dense_support_input_codes

#print axioms dense_support_iterate_codes

#print axioms dense_support_endpoint_step
end IV04.Paper.Computational
