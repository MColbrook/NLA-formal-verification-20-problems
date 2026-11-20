module

public import NLA.IV04.PaperMatrixCoefficientInputSemantics
public import NLA.IV04.PaperMatrixCoefficientInputPaperDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem flat_map_constant_length {α β : Type} (values : List α) (f : α → List β) (k : ℕ)
    (h : ∀ x ∈ values, (f x).length=k) : (values.flatMap f).length=values.length*k := by
  induction values with
  | nil => simp
  | cons x values ih =>
    have hx := h x (by simp)
    have ht : ∀ y ∈ values, (f y).length=k := fun y hy => h y (by simp [hy])
    simp only [List.flatMap_cons,List.length_append,List.length_cons,hx,ih ht]
    ring

theorem dense_endpoint_rationals_length {n : ℕ} (lower upper : RatMat n) :
    (denseEndpointRationals lower upper).length=2*n*n := by
  have hrow (i : Fin n) : ((List.finRange n).flatMap (fun j => [lower i j,upper i j])).length=n*2 := by
    have h := flat_map_constant_length (List.finRange n) (fun j => [lower i j,upper i j]) 2 (by simp)
    simpa only [List.length_finRange] using h
  have h := flat_map_constant_length (List.finRange n)
    (fun i => (List.finRange n).flatMap (fun j => [lower i j,upper i j])) (n*2) (by intro i _; exact hrow i)
  change ((List.finRange n).flatMap (fun i => (List.finRange n).flatMap (fun j => [lower i j,upper i j]))).length=_
  simp only [List.length_finRange] at h
  nlinarith [h]

theorem matrix_endpoint_rationals_length {n : ℕ} (lower upper : RatMat n) (threshold : ℚ) :
    (matrixEndpointRationals lower upper threshold).length=2*n*n+1 := by
  simp only [matrixEndpointRationals,List.length_append,List.length_cons,List.length_nil,
    dense_endpoint_rationals_length]

theorem read_dense_matrix_threshold_code {n : ℕ} (lower upper : RatMat n) (threshold : ℚ) (tail : List Bool) :
    readMatrixRationals (denseMatrixThresholdCode lower upper threshold ++ tail)=
      some (n,matrixEndpointRationals lower upper threshold,tail) := by
  unfold denseMatrixThresholdCode
  rw [List.append_assoc]
  exact read_matrix_rationals_codes n _ tail (matrix_endpoint_rationals_length lower upper threshold)

theorem matrix_coefficient_input_dense_codes {n : ℕ} (lower upper : RatMat n) (threshold : ℚ) (tail : List Bool) :
    ∃ dimension denominator coefficients,
      encodedMatrixCoefficientInput (denseMatrixThresholdCode lower upper threshold ++ tail)=
        Complexity.pair [true] (Complexity.pair dimension
          (Complexity.pair denominator (Complexity.pair (payloadListCode coefficients) tail))) ∧
      wordValue dimension=n ∧ 0 < wordValue denominator ∧
      coefficients.map (fun w => (signedWordValue w : ℚ))=
        (matrixEndpointRationals lower upper threshold).map (fun q => q*(wordValue denominator : ℚ)) ∧
      coefficients.length=2*n*n+1 :=
  matrix_coefficient_input_correct _ n _ tail (read_dense_matrix_threshold_code lower upper threshold tail)

theorem paper_matrix_box_code_eq (P : IV04.Paper.IntegerPartition) :
    P.matrixBoxCode=denseMatrixThresholdCode P.rationalLower P.rationalUpper P.threshold := by
  simp [IV04.Paper.IntegerPartition.matrixBoxCode,denseMatrixThresholdCode,matrixEndpointRationals,
    denseEndpointRationals,List.flatMap_assoc,List.flatMap_append,List.append_assoc]

theorem matrix_coefficient_input_paper_box (P : IV04.Paper.IntegerPartition) :
    ∃ dimension denominator coefficients,
      encodedMatrixCoefficientInput P.matrixBoxCode=
        Complexity.pair [true] (Complexity.pair dimension
          (Complexity.pair denominator (Complexity.pair (payloadListCode coefficients) []))) ∧
      wordValue dimension=P.layerCount ∧ 0 < wordValue denominator ∧
      coefficients.map (fun w => (signedWordValue w : ℚ))=
        (matrixEndpointRationals P.rationalLower P.rationalUpper P.threshold).map
          (fun q => q*(wordValue denominator : ℚ)) ∧
      coefficients.length=2*P.layerCount*P.layerCount+1 := by
  rw [paper_matrix_box_code_eq]
  simpa only [List.append_nil] using matrix_coefficient_input_dense_codes P.rationalLower P.rationalUpper P.threshold []

#print axioms matrix_coefficient_input_paper_box
end IV04.Paper.Computational
