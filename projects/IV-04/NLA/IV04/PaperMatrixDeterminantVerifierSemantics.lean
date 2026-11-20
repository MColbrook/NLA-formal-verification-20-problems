module

public import NLA.IV04.PaperMatrixDeterminantVerifierPoly
public import NLA.IV04.PaperMatrixDenseSupportRational
public import NLA.IV04.PaperBudgetedPowerSemantics
public import NLA.IV04.PaperDenseWordMatrix
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem ordered_matrix_selected_denominator (matrix choices : List Bool) :
    pairFst (pairSnd (pairSnd (encodedOrderedMatrixVertexSelection (pair matrix choices))))=
      pairFst (pairSnd (pairSnd (encodedMatrixCoefficientInput matrix))) := by
  simp only [encodedOrderedMatrixVertexSelection,orderMatrixVertexOutput,encodedMatrixVertexSelection,
    matrixVertexDecoded,pairFst_pair,pairSnd_pair]

theorem matrix_determinant_threshold_argument_code (matrix choices dimension denominator threshold tail rest : List Bool)
    (words : List (List Bool))
    (he : encodedOrderedMatrixVertexSelection (pair matrix choices)=
      pair [true] (pair dimension (pair denominator
        (pair (pair (payloadListCode words) (pair (payloadListCode [threshold]) rest)) tail)))) :
    matrixDeterminantThresholdArgument (pair matrix choices)=
      pair (polynomialDenseIntegerDeterminant (pair dimension (payloadListCode words)))
        (pair threshold (pair denominator (encodedMatrixDenominatorPower matrix))) := by
  simp only [matrixDeterminantThresholdArgument,matrixDeterminantThresholdFields,he,pairFst_pair,pairSnd_pair,payloadListCode]

theorem matrix_determinant_verifier_decode_failure (matrix choices : List Bool)
    (h : readMatrixRationals matrix=none) :
    encodedMatrixDeterminantVerifier (pair matrix choices)=[false] := by
  rw [encodedMatrixDeterminantVerifier,strict_matrix_selection_flag_decode_failure matrix choices h]
  simp [andBit,caseBit₀]

theorem matrix_selected_word_clock (n : ℕ) (dimension : List Bool) (words : List (List Bool))
    (hd : wordValue dimension=n) (hsize : words.length=n*n) :
    wordValue dimension ≤ (pair dimension (payloadListCode words)).length := by
  have hb := payload_list_count_length words
  have hn : n ≤ n*n := by
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_mul,Nat.mul_succ];omega
  rw [hd];simp only [pair_length];omega

theorem matrix_verifier_flag_combine (P Q R S : Prop)
    [Decidable P] [Decidable Q] [Decidable R] [Decidable S] :
    andBit [decide (P ∧ Q)] (andBit [decide R] [decide S])=[decide (P ∧ Q ∧ R ∧ S)] := by
  by_cases hp : P <;> by_cases hq : Q <;> by_cases hr : R <;> by_cases hs : S <;>
    simp [hp,hq,hr,hs,andBit,caseBit₀,caseBit]

theorem matrix_determinant_verifier_rational_input (matrix choices tail : List Bool) (n : ℕ)
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
  obtain ⟨dimension,denominator,rows,tword,hd,hD,hrsize,hrows,hT,hout⟩ :=
    ordered_matrix_vertex_selection_rational_input matrix choices tail n pairs threshold hread hsize horder hchoices
  refine ⟨dimension,denominator,rows,tword,hd,hD,hrsize,hrows,hT,?_⟩
  have hpower := (matrix_denominator_power_successful_input matrix n _ tail hread).1
  have hden : pairFst (pairSnd (pairSnd (encodedMatrixCoefficientInput matrix)))=denominator := by
    rw [← ordered_matrix_selected_denominator matrix choices,hout]
    simp only [pairFst_pair,pairSnd_pair]
  rw [hden] at hpower
  let words := selectedEndpointWords rows choices
  have hwordsize : words.length=n*n := (selected_endpoint_words_length rows choices).trans hrsize
  have hk := matrix_selected_word_clock n dimension words hd hwordsize
  have hE : (signedWordValue (polynomialDenseIntegerDeterminant (pair dimension (payloadListCode words))) : ℚ)/
      (wordValue denominator : ℚ)^n=
        (rationalContinuantMatrix n
          (commonDenominatorCoefficients (denseWordDiagonal n words) (wordValue denominator))
          (commonDenominatorCoefficients (denseWordLower n words) (wordValue denominator))
          (commonDenominatorCoefficients (denseWordUpper n words) (wordValue denominator))).det := by
    rw [dense_integer_determinant_word_code dimension words hk,hd]
    exact (common_denominator_determinant n _ _ _ (wordValue denominator) hD).symm
  have ht := scaled_determinant_threshold_correct
    (polynomialDenseIntegerDeterminant (pair dimension (payloadListCode words))) tword denominator
    (encodedMatrixDenominatorPower matrix) n _ threshold hD hpower hE hT
  rw [encodedMatrixDeterminantVerifier,strict_matrix_selection_rational_input matrix choices tail n pairs threshold hread hsize horder hchoices]
  simp only [pairFst_pair]
  rw [matrix_dense_support_rational_input matrix tail n pairs threshold hread hsize,
    matrix_determinant_threshold_argument_code matrix choices dimension denominator tword tail
      (choices.drop (n*n)) words hout,ht]
  exact matrix_verifier_flag_combine _ _ _ _

#print axioms matrix_determinant_verifier_rational_input
end IV04.Paper.Computational