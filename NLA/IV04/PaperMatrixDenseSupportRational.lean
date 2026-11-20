module

public import NLA.IV04.PaperMatrixDenseSupport
public import NLA.IV04.PaperMatrixDenseSupportReference
public import NLA.IV04.PaperMatrixVertexSelectionBridge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem dense_endpoint_all_scaled (n i j D : ℕ) (rows : List (List Bool × List Bool))
    (pairs : List (ℚ × ℚ)) (hD : 0 < D)
    (hrows : rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
      pairs.map (fun row => (row.1*(D : ℚ),row.2*(D : ℚ)))) :
    denseEndpointAll n i j rows ↔ rationalDenseEndpointAll n i j pairs := by
  have hDn : (D : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  induction rows generalizing pairs i j with
  | nil => cases pairs <;> simp_all [denseEndpointAll,rationalDenseEndpointAll]
  | cons row rows ih =>
    obtain ⟨lower,upper⟩ := row
    cases pairs with
    | nil => simp at hrows
    | cons pair pairs =>
      obtain ⟨a,b⟩ := pair
      have hhead : ((signedWordValue lower : ℚ),(signedWordValue upper : ℚ))=(a*(D : ℚ),b*(D : ℚ)) :=
        (List.cons.inj hrows).1
      have htail := (List.cons.inj hrows).2
      have hl : signedWordValue lower=0 ↔ a=0 := by
        have he := congrArg Prod.fst hhead
        change (signedWordValue lower : ℚ)=a*(D : ℚ) at he
        constructor
        · intro hz;rw [hz,Int.cast_zero] at he;exact (mul_eq_zero.mp he.symm).resolve_right hDn
        · intro hz;rw [hz,zero_mul] at he;exact_mod_cast he
      have hu : signedWordValue upper=0 ↔ b=0 := by
        have he := congrArg Prod.snd hhead
        change (signedWordValue upper : ℚ)=b*(D : ℚ) at he
        constructor
        · intro hz;rw [hz,Int.cast_zero] at he;exact (mul_eq_zero.mp he.symm).resolve_right hDn
        · intro hz;rw [hz,zero_mul] at he;exact_mod_cast he
      simpa only [denseEndpointAll,rationalDenseEndpointAll,hl,hu] using
        and_congr (Iff.rfl : ((i ≤ j+1 ∧ j ≤ i+1) ∨ (a=0 ∧ b=0)) ↔ _)
          (ih (if n ≤ j+1 then i+1 else i) (if n ≤ j+1 then 0 else j+1) pairs htail)

theorem matrix_dense_support_rational_input (matrix tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) :
    encodedMatrixDenseSupportFlag matrix=[decide (rationalDenseEndpointAll n 0 0 pairs)] := by
  obtain ⟨dimension,denominator,coefficients,hdecoded,hdim,hD,hvalues,_⟩ :=
    matrix_coefficient_input_correct matrix n _ tail hread
  obtain ⟨rows,tword,hcoefficients,hrows,hthreshold⟩ :=
    scaled_endpoint_words_split pairs threshold (wordValue denominator) coefficients hvalues
  have hlen : rows.length=pairs.length := by
    have h := congrArg List.length hrows
    simpa only [List.length_map] using h
  have hrsize : rows.length=n*n := hlen.trans hsize
  have htable : payloadListCode coefficients=endpointWordPairsCode rows (payloadListCode [tword]) := by
    rw [endpoint_word_pairs_code_flatten,hcoefficients]
  rw [htable] at hdecoded
  rw [encoded_matrix_dense_support_flag_code matrix n true dimension denominator tail rows
    (payloadListCode [tword]) hdecoded hdim hrsize]
  simp only [Bool.true_and]
  apply congrArg (fun flag : Bool => [flag])
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact dense_endpoint_all_scaled n 0 0 (wordValue denominator) rows pairs hD hrows

#print axioms matrix_dense_support_rational_input
end IV04.Paper.Computational
