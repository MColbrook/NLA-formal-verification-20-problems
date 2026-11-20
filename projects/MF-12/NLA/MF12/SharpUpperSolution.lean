module

public import NLA.MF12.PaperSharpUpper

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator
namespace NLA.MF12.Paper

theorem paper_sourceV_sharp_norm : ‖sourceV‖ = Real.sqrt 2 := by
  exact sourceV_sharp_norm

theorem paper_sourceU_sharp_norm : ‖sourceU‖ = Real.sqrt 3 := by
  exact sourceU_sharp_norm

theorem paper_parameter_power_sharp_norm (lam μ : ℝ) (hlam : 0 < lam)
    (hμ : 0 < μ) (hlμ : lam ≤ μ) (hμ1 : μ < 1) (q : ℕ) :
    spectralNorm (parameterMatrix lam μ ^ q) ≤ (1-μ)⁻¹ := by
  exact parameter_power_sharp_norm lam μ hlam hμ hlμ hμ1 q

theorem paper_compressed_sharp_norm (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) (qs : List ℕ) :
    ‖matrixProduct (qs.map (parameterCompressed lam (Real.rpow lam (1-α))))‖ ≤
      1+Real.rpow (qs.sum : ℝ) α := by
  exact compressed_sharp_norm lam α hlam hlamq hα hα1 qs

theorem paper_parameter_reset_factorization (lam μ : ℝ) (q₀ qlast : ℕ) (qs : List ℕ) :
    binaryProduct (parameterMatrix lam μ) resetMatrix (gapWord (q₀ :: (qs ++ [qlast]))) =
      parameterMatrix lam μ ^ qlast * sourceV *
        matrixProduct (qs.map (parameterCompressed lam μ)) * sourceU * parameterMatrix lam μ ^ q₀ := by
  exact parameter_reset_factorization lam μ q₀ qlast qs

theorem paper_parameter_all_word_sharp_upper (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) (w : List Bool) (hw : 1 ≤ w.length) :
    spectralNorm (binaryProduct (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix w) ≤
      (2*Real.sqrt 6/(1-Real.rpow lam (1-α))^2)*Real.rpow (w.length : ℝ) α := by
  exact parameter_all_word_sharp_upper lam α hlam hlamq hα hα1 w hw

theorem paper_parameter_family_sharp_upper (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth (pairFamily (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix) n ≤
      (2*Real.sqrt 6/(1-Real.rpow lam (1-α))^2)*Real.rpow (n : ℝ) α := by
  exact parameter_family_sharp_upper lam α hlam hlamq hα hα1 n hn

#print axioms paper_sourceV_sharp_norm
#print axioms paper_sourceU_sharp_norm
#print axioms paper_parameter_power_sharp_norm
#print axioms paper_compressed_sharp_norm
#print axioms paper_parameter_reset_factorization
#print axioms paper_parameter_all_word_sharp_upper
#print axioms paper_parameter_family_sharp_upper

end NLA.MF12.Paper
