module

public import NLA.MI22.PaperProductError

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace NLA.MI22.Paper

theorem paper_Y_seventh :
    (spectralPower paperB (1/8))^(7 : ℕ) = spectralPower paperB (7/8) := by
  rw [← spectralPower_nat _ (spectralPower_posDef paperB paperB_posDef (1/8)) 7]
  have h := CFC.rpow_rpow paperB (1/8 : ℝ) (7 : ℝ)
    (by norm_num) paperB_posDef.isStrictlyPositive
  change spectralPower (spectralPower paperB (1/8)) 7 =
    spectralPower paperB ((1/8)*7) at h
  norm_num only [Nat.cast_ofNat]
  convert h using 1 <;> norm_num

theorem paper_left_formula :
    leftProduct witnessA paperB (1/8) =
      witnessAFiveEighths*spectralPower paperC (1/8)*witnessD*
        (spectralPower paperB (1/8))^7 := by
  rw [leftProduct, weightedMean, witnessA_eighth, witnessA_half,
    witnessA_negative_half, paperC_normalized,
    show (1 : ℝ)-1/8=7/8 by norm_num, ← paper_Y_seventh]
  simp only [← mul_assoc, witnessAOneEighth_mul_D]

theorem real_entry_le_operatorNorm {n : ℕ} (A : Mat n) (i j : Fin n) :
    (A i j).re ≤ operatorNorm A := by
  let e : EuclideanSpace ℂ (Fin n) := PiLp.single 2 j (1 : ℂ)
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hentry : (T e) i = A i j := by
    change (Matrix.mulVec A (Pi.single j (1 : ℂ))) i = A i j
    simp [Matrix.mulVec_single_one]
  have h := (euclidean_norm_bounds_proved A).2 e i
  change ‖(T e) i‖ ≤ operatorNorm A*‖e‖ at h
  rw [hentry, he, mul_one] at h
  exact (Complex.re_le_norm _).trans h

theorem paper_left_norm_gt : 10900 < operatorNorm (leftProduct witnessA paperB (1/8)) := by
  rw [paper_left_formula, operatorNorm_eq_l2]
  let L := witnessAFiveEighths*spectralPower paperC (1/8)*witnessD*
    (spectralPower paperB (1/8))^7
  let T := witnessAFiveEighths*paperR*witnessD*paperS^7
  change 10900 < ‖L‖
  have herr : ‖L-T‖ < 100 := paper_product_error
  have hentry : 11000 < (T 0 1).re := paper_approx_entry
  have hnorm : (T 0 1).re ≤ ‖T‖ := by
    simpa only [operatorNorm_eq_l2] using real_entry_le_operatorNorm T 0 1
  have htri : ‖T‖ ≤ ‖L‖+‖L-T‖ := by
    calc
      ‖T‖ = ‖L-(L-T)‖ := by congr 1; abel
      _ ≤ ‖L‖+‖L-T‖ := norm_sub_le _ _
  linarith

theorem printed_counterexample :
    witnessA.PosDef ∧ paperB.PosDef ∧
    10900 < operatorNorm (leftProduct witnessA paperB (1/8)) ∧
    operatorNorm (witnessA*paperB) < 10200 ∧
    ¬ SingularLogMajorized (leftProduct witnessA paperB (1/8)) (witnessA*paperB) := by
  refine ⟨witnessA_posDef,paperB_posDef,paper_left_norm_gt,paperAB_norm_lt,?_⟩
  intro h
  have hfirst := h.1 1 (by norm_num) (by norm_num)
  simp only [singularPrefix, Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at hfirst
  rw [singularValue_zero_eq_operatorNorm (by norm_num),
    singularValue_zero_eq_operatorNorm (by norm_num)] at hfirst
  linarith [paper_left_norm_gt,paperAB_norm_lt]

#print axioms printed_counterexample
end NLA.MI22.Paper
