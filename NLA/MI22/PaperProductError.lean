module

public import NLA.MI22.PaperRootErrors
public import NLA.MI22.SingularValues

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace NLA.MI22.Paper

theorem norm_power_difference {E : Type*} [NormedRing E] [NormOneClass E]
    (A B : E) (K e : ℝ) (hK : 0 ≤ K) (he : 0 ≤ e)
    (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ K) (hAB : ‖A-B‖ ≤ e) (n : ℕ) :
    ‖A^n-B^n‖ ≤ (n : ℝ)*K^(n-1)*e := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : ‖A^n‖ ≤ K^n := (norm_pow_le A n).trans
      (pow_le_pow_left₀ (norm_nonneg A) hA n)
    calc
      ‖A^(n+1)-B^(n+1)‖ = ‖A^n*(A-B)+(A^n-B^n)*B‖ := by
        congr 1
        rw [pow_succ, pow_succ]
        noncomm_ring
      _ ≤ ‖A^n‖*‖A-B‖+‖A^n-B^n‖*‖B‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ K^n*e+((n : ℝ)*K^(n-1)*e)*K := add_le_add
        (mul_le_mul hpow hAB (norm_nonneg _) (pow_nonneg hK _))
        (mul_le_mul ih hB (norm_nonneg _) (by positivity))
      _ = ((n+1 : ℕ) : ℝ)*K^((n+1)-1)*e := by
        cases n with
        | zero => simp
        | succ n => simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ]; ring

theorem norm_mul_four_le {E : Type*} [NormedRing E] (A B C D : E) :
    ‖A*B*C*D‖ ≤ ‖A‖*‖B‖*‖C‖*‖D‖ :=
  (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
      (norm_mul_le _ _) (norm_nonneg C))) (norm_nonneg D))

theorem paperR_norm_le : ‖paperR‖ ≤ 8 := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap paperR (by norm_num)
    paperR_posDef.posSemidef.nonneg).mpr
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (Matrix.le_iff.mpr paperR_upper_posDef.posSemidef)

theorem paperS_norm_le : ‖paperS‖ ≤ 4 := by
  apply (CStarAlgebra.norm_le_iff_le_algebraMap paperS (by norm_num)
    paperS_posDef.posSemidef.nonneg).mpr
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (Matrix.le_iff.mpr paperS_upper_posDef.posSemidef)

theorem paperD_norm_le : ‖witnessD‖ ≤ 16 := by
  rw [witnessD, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)).mpr
  intro i
  fin_cases i <;> norm_num

theorem paperD5_norm_le : ‖witnessAFiveEighths‖ ≤ 32 := by
  rw [witnessAFiveEighths, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 32)).mpr
  intro i
  fin_cases i <;> norm_num

theorem paper_product_error :
    ‖witnessAFiveEighths*spectralPower paperC (1/8)*witnessD*
        (spectralPower paperB (1/8))^7 -
      witnessAFiveEighths*paperR*witnessD*paperS^7‖ < 100 := by
  let X := spectralPower paperC (1/8)
  let Y := spectralPower paperB (1/8)
  let e : ℝ := 64/100000000
  have hx : ‖X-paperR‖ ≤ e := by simpa only [operatorNorm_eq_l2] using paperX_error.le
  have hy : ‖Y-paperS‖ ≤ e := by simpa only [operatorNorm_eq_l2] using paperY_error.le
  have hY : ‖Y‖ ≤ 4 := by simpa only [operatorNorm_eq_l2] using paperY_norm_lt.le
  have hY7 : ‖Y^7‖ ≤ (4 : ℝ)^7 :=
    (norm_pow_le Y 7).trans (pow_le_pow_left₀ (norm_nonneg Y) hY 7)
  have hdiff : ‖Y^7-paperS^7‖ ≤ 7*(4 : ℝ)^6*e := by
    simpa only [Nat.cast_ofNat, Nat.add_one_sub_one] using
      norm_power_difference Y paperS 4 e (by norm_num) (by dsimp [e]; positivity)
        hY paperS_norm_le hy 7
  change ‖witnessAFiveEighths*X*witnessD*Y^7-witnessAFiveEighths*paperR*witnessD*paperS^7‖ < 100
  calc
    _ = ‖witnessAFiveEighths*(X-paperR)*witnessD*Y^7+
        witnessAFiveEighths*paperR*witnessD*(Y^7-paperS^7)‖ := by congr 1; noncomm_ring
    _ ≤ ‖witnessAFiveEighths*(X-paperR)*witnessD*Y^7‖+
        ‖witnessAFiveEighths*paperR*witnessD*(Y^7-paperS^7)‖ := norm_add_le _ _
    _ ≤ (32*e*16*4^7)+(32*8*16*(7*4^6*e)) := by
      apply add_le_add
      · apply (norm_mul_four_le _ _ _ _).trans
        gcongr
        · exact paperD5_norm_le
        · exact paperD_norm_le
      · apply (norm_mul_four_le _ _ _ _).trans
        gcongr
        · exact paperD5_norm_le
        · exact paperR_norm_le
        · exact paperD_norm_le
    _ < 100 := by norm_num [e]

#print axioms paper_product_error
end NLA.MI22.Paper
