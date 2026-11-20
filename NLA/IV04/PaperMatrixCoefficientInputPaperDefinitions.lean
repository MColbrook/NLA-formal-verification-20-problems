module

public import NLA.IV04.PaperMatrixCoefficientInputDefinitions
public import NLA.IV04.PaperRationalContinuantDefinitions
public import NLA.IV04.PaperEncodingDefinitions
public import Mathlib.Data.List.FinRange

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def denseEndpointRationals {n : ℕ} (lower upper : RatMat n) : List ℚ :=
  (List.finRange n).flatMap (fun i => (List.finRange n).flatMap (fun j => [lower i j,upper i j]))

def matrixEndpointRationals {n : ℕ} (lower upper : RatMat n) (threshold : ℚ) : List ℚ :=
  denseEndpointRationals lower upper ++ [threshold]

def denseMatrixThresholdCode {n : ℕ} (lower upper : RatMat n) (threshold : ℚ) : List Bool :=
  IV04.Paper.naturalCode n ++ (matrixEndpointRationals lower upper threshold).flatMap IV04.Paper.rationalCode

end IV04.Paper.Computational
