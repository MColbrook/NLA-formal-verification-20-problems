module

public import NLA.RA09.SpectralOptimality.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace RootRA09SpectralOptimality
open NLA.RA09

def sharpA2 : RealMatrix 2 := Matrix.diagonal ![2,1]
def sharpB2 : RealMatrix 2 := Matrix.diagonal ![1,0]

def sharpDataA2 : OrderedSpectralData sharpA2 where
  eigenvalues := ![2,1]
  orthogonal := 1
  decreasing := by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *
  nonnegative := by intro i; fin_cases i <;> norm_num
  reconstruct := by simp [sharpA2]

def sharpDataB2 : OrderedSpectralData sharpB2 where
  eigenvalues := ![1,0]
  orthogonal := 1
  decreasing := by intro i j hij; fin_cases i <;> fin_cases j <;> norm_num at *
  nonnegative := by intro i; fin_cases i <;> norm_num
  reconstruct := by simp [sharpB2]

end RootRA09SpectralOptimality
