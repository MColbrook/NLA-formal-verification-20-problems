module

public import NLA.MF12.PaperSharpCompressed

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator
namespace NLA.MF12.Paper

theorem parameter_all_word_sharp_upper (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) (w : List Bool) (hw : 1 ≤ w.length) :
    spectralNorm (binaryProduct (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix w) ≤
      (2*Real.sqrt 6/(1-Real.rpow lam (1-α))^2)*Real.rpow (w.length : ℝ) α := by
  let μ := Real.rpow lam (1-α)
  let H := (1-μ)⁻¹
  let R := Real.rpow (w.length : ℝ) α
  have hμ : 0 < μ := Real.rpow_pos_of_pos hlam _
  have hμ1 : μ < 1 := Real.rpow_lt_one hlam.le (by linarith) (by linarith)
  have hlμ : lam ≤ μ := by
    simpa [μ] using Real.rpow_le_rpow_of_exponent_ge hlam (by linarith : lam ≤ 1)
      (by linarith : 1-α ≤ 1)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hH1 : 1 ≤ H := by
    dsimp [H]
    rw [one_le_inv₀ (by linarith)]
    linarith
  have hR : 1 ≤ R := Real.one_le_rpow (by exact_mod_cast hw) hα.le
  have hs : 1 ≤ Real.sqrt 6 := by
    have hp := Real.sqrt_nonneg (6:ℝ)
    have he := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6)
    nlinarith
  have hconst : H ≤ 2*Real.sqrt 6*H^2 := by
    calc
      H ≤ H^2 := by nlinarith
      _ ≤ (2*Real.sqrt 6)*H^2 := by
        simpa using mul_le_mul_of_nonneg_right (by linarith : 1 ≤ 2*Real.sqrt 6) (sq_nonneg H)
  have hcoeff : 2*Real.sqrt 6/(1-μ)^2 = 2*Real.sqrt 6*H^2 := by
    simp only [H, div_eq_mul_inv, inv_pow]
  change _ ≤ (2*Real.sqrt 6/(1-μ)^2)*R
  rw [hcoeff]
  obtain ⟨qs, hne, hword, hlength⟩ := gap_decomposition w
  cases qs with
  | nil => exact False.elim (hne rfl)
  | cons q₀ tail =>
      rcases List.eq_nil_or_concat' tail with hnil | ⟨mid, qlast, htail⟩
      · subst tail
        have hprod : binaryProduct (parameterMatrix lam μ) resetMatrix w =
            parameterMatrix lam μ ^ q₀ := by
          rw [← hword]
          simp only [gapWord_singleton, binaryProduct_replicate_false]
        change spectralNorm (binaryProduct (parameterMatrix lam μ) resetMatrix w) ≤ _
        rw [hprod]
        calc
          _ ≤ H := parameter_power_sharp_norm lam μ hlam hμ hlμ hμ1 q₀
          _ ≤ 2*Real.sqrt 6*H^2 := hconst
          _ ≤ (2*Real.sqrt 6*H^2)*R := by
            simpa using mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 2*Real.sqrt 6*H^2)
      · subst tail
        have hmid : mid.sum ≤ w.length := by
          simp only [List.sum_cons, List.sum_append, List.sum_singleton,
            List.length_cons, List.length_append, List.length_singleton] at hlength
          omega
        have hmidpow : Real.rpow (mid.sum : ℝ) α ≤ R :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hmid) hα.le
        have hB : ‖matrixProduct (mid.map (parameterCompressed lam μ))‖ ≤ 1+R :=
          (compressed_sharp_norm lam α hlam hlamq hα hα1 mid).trans (by linarith)
        change spectralNorm (binaryProduct (parameterMatrix lam μ) resetMatrix w) ≤ _
        rw [← hword, parameter_reset_factorization]
        calc
          _ ≤ Real.sqrt 6*H^2*(1+R) := parameter_factor_sharp_norm lam μ hlam hμ hlμ hμ1
            q₀ qlast _ (1+R) (by linarith) hB
          _ ≤ Real.sqrt 6*H^2*(2*R) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ = (2*Real.sqrt 6*H^2)*R := by ring

/-- The exact printed general-parameter all-length upper constant. -/
theorem parameter_family_sharp_upper (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth (pairFamily (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix) n ≤
      (2*Real.sqrt 6/(1-Real.rpow lam (1-α))^2)*Real.rpow (n : ℝ) α := by
  apply familyGrowth_le_of_binary
  intro w hw
  simpa [hw] using parameter_all_word_sharp_upper lam α hlam hlamq hα hα1 w (by omega)

#print axioms parameter_family_sharp_upper
end NLA.MF12.Paper
