module

public import NLA.IV04.PaperMatrixVerifierNP
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_encoded_matrix_determinant_verifier_mem_fp : encodedMatrixDeterminantVerifier ∈ FP := by
  exact encoded_matrix_determinant_verifier_mem_fp

theorem verified_matrix_determinant_verifier_decode_failure (matrix choices : List Bool)
    (h : readMatrixRationals matrix=none) :
    encodedMatrixDeterminantVerifier (pair matrix choices)=[false] := by
  exact matrix_determinant_verifier_decode_failure matrix choices h

theorem verified_matrix_determinant_verifier_rational_input (matrix choices tail : List Bool) (n : ℕ)
    (pairs : List (ℚ × ℚ)) (threshold : ℚ)
    (hread : readMatrixRationals matrix=some
      (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],tail))
    (hsize : pairs.length=n*n) (horder : ∀ row ∈ pairs, row.1 ≤ row.2)
    (hchoices : n*n ≤ choices.length) :
    ∃ dimension denominator : List Bool, ∃ rows : List (List Bool × List Bool), ∃ thresholdWord : List Bool,
      wordValue dimension=n ∧ 0 < wordValue denominator ∧ rows.length=n*n ∧
      rows.map (fun row => ((signedWordValue row.1 : ℚ),(signedWordValue row.2 : ℚ)))=
        pairs.map (fun row => (row.1*(wordValue denominator : ℚ),row.2*(wordValue denominator : ℚ))) ∧
      (signedWordValue thresholdWord : ℚ)=threshold*(wordValue denominator : ℚ) ∧
      encodedMatrixDeterminantVerifier (pair matrix choices)=
        [decide (tail=[] ∧ choices.length=n*n ∧ rationalDenseEndpointAll n 0 0 pairs ∧
          threshold ≤ (rationalContinuantMatrix n
            (commonDenominatorCoefficients (denseWordDiagonal n (selectedEndpointWords rows choices)) (wordValue denominator))
            (commonDenominatorCoefficients (denseWordLower n (selectedEndpointWords rows choices)) (wordValue denominator))
            (commonDenominatorCoefficients (denseWordUpper n (selectedEndpointWords rows choices)) (wordValue denominator))).det)] := by
  exact matrix_determinant_verifier_rational_input matrix choices tail n pairs threshold hread hsize horder hchoices

theorem verified_dense_word_matrix_equals_continuant (n D : ℕ) (words : List (List Bool))
    (htri : RationalTridiagonal (denseWordRationalMatrix n D words)) :
    denseWordRationalMatrix n D words=
      rationalContinuantMatrix n (commonDenominatorCoefficients (denseWordDiagonal n words) D)
        (commonDenominatorCoefficients (denseWordLower n words) D)
        (commonDenominatorCoefficients (denseWordUpper n words) D) := by
  exact dense_word_matrix_equals_continuant n D words htri

theorem verified_dense_word_matrix_determinant (n D : ℕ) (words : List (List Bool))
    (hsize : words.length=n*n) (hD : 0 < D)
    (htri : RationalTridiagonal (denseWordRationalMatrix n D words)) :
    (denseWordRationalMatrix n D words).det=
      (signedWordValue (polynomialDenseIntegerDeterminant (Complexity.pair n.bits (payloadListCode words))) : ℚ)/(D : ℚ)^n := by
  exact dense_word_matrix_determinant n D words hsize hD htri

theorem verified_encoded_matrix_bounded_witness_mem_fp : encodedMatrixBoundedWitnessFlag ∈ FP := by
  exact encoded_matrix_bounded_witness_mem_fp

theorem verified_matrix_bounded_witness_flag_pair_language (input : List Bool) :
    encodedMatrixBoundedWitnessFlag input=[true] ↔ input ∈ pairLang matrixBoundedWitness := by
  exact matrix_bounded_witness_flag_pair_language input

theorem verified_matrix_bool_fp_language {f : List Bool → List Bool} (hfp : f ∈ FP)
    {L : Language} (hflag : ∀ input, f input=[true] ∨ f input=[false])
    (hcorrect : ∀ input, f input=[true] ↔ input ∈ L) : L ∈ P := by
  exact matrix_bool_fp_language hfp hflag hcorrect

theorem verified_matrix_bounded_pair_language_mem_p : pairLang matrixBoundedWitness ∈ P := by
  exact matrix_bounded_pair_language_mem_p

theorem verified_matrix_verifier_language_mem_np : matrixVerifierLanguage ∈ NP := by
  exact matrix_verifier_language_mem_np

#print axioms IV04.Paper.Computational.verified_encoded_matrix_determinant_verifier_mem_fp
#print axioms IV04.Paper.Computational.verified_matrix_determinant_verifier_decode_failure
#print axioms IV04.Paper.Computational.verified_matrix_determinant_verifier_rational_input
#print axioms IV04.Paper.Computational.verified_dense_word_matrix_equals_continuant
#print axioms IV04.Paper.Computational.verified_dense_word_matrix_determinant
#print axioms IV04.Paper.Computational.verified_encoded_matrix_bounded_witness_mem_fp
#print axioms IV04.Paper.Computational.verified_matrix_bounded_witness_flag_pair_language
#print axioms IV04.Paper.Computational.verified_matrix_bool_fp_language
#print axioms IV04.Paper.Computational.verified_matrix_bounded_pair_language_mem_p
#print axioms IV04.Paper.Computational.verified_matrix_verifier_language_mem_np
end IV04.Paper.Computational
