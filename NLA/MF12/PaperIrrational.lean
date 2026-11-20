module

public import NLA.MF12.PaperRationalRealization
public import Mathlib.NumberTheory.Real.Irrational

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

theorem log_three_four_irrational : Irrational (Real.log 3 / Real.log 4) := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rintro ⟨q, hq⟩
  have hqpos : 0 < q := Rat.cast_pos.mp (by rw [hq]; exact div_pos h3 h4)
  have hqrepr : (q : ℝ) = (q.num.toNat : ℝ)/(q.den : ℝ) := by
    rw [Rat.cast_def, ← Int.toNat_of_nonneg (Rat.num_nonneg.mpr hqpos.le)]
    simp only [Int.cast_natCast, Int.toNat_natCast]
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
  have he : (q.den : ℝ)*Real.log 3 = (q.num.toNat : ℝ)*Real.log 4 := by
    rw [hqrepr] at hq
    simpa only [mul_comm] using ((div_eq_div_iff hden h4.ne').mp hq).symm
  have hpR : (3 : ℝ)^q.den = (4 : ℝ)^q.num.toNat := by
    apply Real.log_injOn_pos (show 0 < (3 : ℝ)^q.den by positivity)
      (show 0 < (4 : ℝ)^q.num.toNat by positivity)
    simpa only [Real.log_pow] using he
  have hp : (3 : ℕ)^q.den = (4 : ℕ)^q.num.toNat := by exact_mod_cast hpR
  have hd : 3 ∣ (4 : ℕ)^q.num.toNat := by
    rw [← hp]
    exact dvd_pow_self _ q.den_nz
  have hbad : (3 : ℕ) ∣ 4 := (by norm_num : Nat.Prime 3).dvd_of_dvd_pow hd
  norm_num at hbad

theorem irrational_exponent_bounds :
    0 < 1-Real.log 3/Real.log 4 ∧ 1-Real.log 3/Real.log 4 < 1 ∧
      Irrational (1-Real.log 3/Real.log 4) := by
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h34 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  refine ⟨by have := (div_lt_one h4).mpr h34; linarith,
    by have := div_pos h3 h4; linarith, ?_⟩
  simpa only [Rat.cast_one] using log_three_four_irrational.ratCast_sub (1 : ℚ)

theorem irrational_base_mu : baseMu (1-Real.log 3/Real.log 4) = 1/3 := by
  have h4 : Real.log 4 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ)<4)).ne'
  unfold baseMu baseLambda
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos (by norm_num), Real.log_div (by norm_num) (by norm_num), Real.log_one]
  have he : (0-Real.log 4)*(1-(1-Real.log 3/Real.log 4)) = -Real.log 3 := by
    field_simp
    <;> ring
  rw [he, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

theorem dyadic_is_rational {x : ℝ} (hx : IsDyadic x) : ∃ q : ℚ, (q : ℝ) = x := by
  obtain ⟨z, k, rfl⟩ := hx
  refine ⟨(z : ℚ)/(2 : ℚ)^k, ?_⟩
  simp

theorem irrational_pair_entries (i j : Fin 6) :
    (∃ q : ℚ, (q : ℝ) = fractionalMatrix (1-Real.log 3/Real.log 4) i j) ∧
    (∃ q : ℚ, (q : ℝ) = resetMatrix i j) := by
  constructor
  · refine ⟨(!![1,0,0,0,0,0; 0,1/4,1/4,0,0,0; 0,0,1/4,0,0,0;
      0,0,0,1/3,1/3,0; 0,0,0,0,1/3,0; 0,0,0,0,0,1] : Matrix (Fin 6) (Fin 6) ℚ) i j, ?_⟩
    fin_cases i <;> fin_cases j <;>
      norm_num [fractionalMatrix, baseLambda, irrational_base_mu]
  · exact dyadic_is_rational (reset_entries_dyadic i j)

theorem irrational_pair_realization :
    Realizes (fractionalMatrix (1-Real.log 3/Real.log 4)) resetMatrix
      (1-Real.log 3/Real.log 4) := by
  have h := irrational_exponent_bounds
  simpa only [Realizes, pow_one] using powered_fractional_realization _ h.1 h.2.1 1 le_rfl

theorem rational_exponents_dense (x ε : ℝ) (hx : 0 ≤ x) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 ≤ γ ∧ |γ-x| < ε ∧
      ∃ d : ℕ, 1 ≤ d ∧ ∃ A P : Square d, Realizes A P γ ∧
        ∀ i j, (∃ q : ℚ, (q : ℝ) = A i j) ∧ (∃ q : ℚ, (q : ℝ) = P i j) := by
  obtain ⟨q, hxq, hqx⟩ := exists_rat_btwn (show x < x+ε by linarith)
  have hq : 0 ≤ q := Rat.cast_nonneg.mp (hx.trans hxq.le)
  obtain ⟨d, _, hd, A, P, hg, hdy⟩ := rational_dyadic_realization q hq
  refine ⟨(q : ℝ), hx.trans hxq.le, ?_, d, hd, A, P, hg, ?_⟩
  · rw [abs_of_pos (sub_pos.mpr hxq)]
    linarith
  · intro i j
    exact ⟨dyadic_is_rational (hdy i j).1, dyadic_is_rational (hdy i j).2⟩

#print axioms irrational_pair_realization
#print axioms rational_exponents_dense
end NLA.MF12.Paper
