module

public import NLA.IE21.LiteralWrappers.Concentration

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace NLA.IE21.LiteralWrappers

theorem indicator_trim_replacement {m : ℕ} (hm : 1 ≤ m)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i)
    (b L : ℝ) (hb : 0 ≤ b) (hbL : b ≤ L)
    (hcount : retainedRows θ m ≤ (Finset.univ.filter (fun i => y i ≤ L)).card)
    (P ε : ℝ) (hε : 0 ≤ ε)
    (hW : |(∑ i, if y i ≤ b then (1 : ℝ) else 0)/m-θ| ≤ ε)
    (hZ : |(∑ i, if y i ≤ b then y i else 0)/m-P| ≤ b*ε) :
    |(retainedRows θ m : ℝ) - ((Finset.univ.filter (fun i => y i ≤ b)).card : ℝ)| ≤ m*ε+1 ∧
    |finiteTrim (retainedRows θ m) y - (∑ i, if y i ≤ b then y i else 0)| ≤ L*(m*ε+1) ∧
    |finiteTrim (retainedRows θ m) y/m-P| ≤ 2*L*ε+L/m := by
  classical
  let w : Fin m → ℝ := fun i => if y i ≤ b then 1 else 0
  have hw (i : Fin m) : 0 ≤ w i ∧ w i ≤ 1 := by dsimp [w]; split_ifs <;> norm_num
  have hs : (∑ i, w i) = ((Finset.univ.filter (fun i => y i ≤ b)).card : ℝ) := by simp [w]
  have hz : (∑ i, y i * w i) = ∑ i, if y i ≤ b then y i else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w]
    split_ifs <;> simp
  have halign (i : Fin m) : max (b-y i) 0 = (b-y i)*w i := by
    dsimp [w]
    split_ifs with h
    · rw [mul_one, max_eq_left (sub_nonneg.mpr h)]
    · rw [mul_zero, max_eq_right (sub_nonpos.mpr (le_of_not_ge h))]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hwerr : |(∑ i, w i)-m*θ| ≤ m*ε := by
    rw [mean_deviation_scale hm]
    exact mul_le_mul_of_nonneg_left hW hm0.le
  have hzerr : |(∑ i, y i*w i)-m*P| ≤ m*L*ε := by
    rw [hz, mean_deviation_scale hm]
    have hbe : b*ε ≤ L*ε := mul_le_mul_of_nonneg_right hbL hε
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hZ.trans hbe) hm0.le
  have hk := retainedRows_bounds θ hθ m
  have hdiff : |(retainedRows θ m : ℝ)-∑ i, w i| ≤ m*ε+1 := by
    have h := abs_sub_le (retainedRows θ m : ℝ) (m*θ) (∑ i, w i)
    rw [abs_sub_comm (m*θ)] at h
    linarith [hk.2.2]
  refine ⟨by simpa [hs] using hdiff, ?_, ?_⟩
  · have h := finiteTrim_fractional_error hm (retainedRows θ m) hk.1 y w hy hw b L hb hbL halign hcount
    rw [hz] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdiff (hb.trans hbL))
  · exact finiteTrim_fractional_mean_error hm θ hθ y w hy hw b L hb hbL halign hcount P ε hε hwerr hzerr

theorem zero_retained_shortcut {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω) (hmean : ∫ ω, Y ω ∂μ = 1)
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) (m : ℕ) (hm : 1 ≤ m) (hk : retainedRows θ m = 0) :
    populationTrim θ μ Y ≤ θ ∧ θ < 1/(m : ℝ) := by
  refine ⟨mean_one_trim_le_theta μ Y hY hY0 hmean θ hθ, ?_⟩
  have hh := Nat.lt_floor_add_one (θ*(m : ℝ))
  change θ*(m : ℝ) < (retainedRows θ m : ℝ)+1 at hh
  rw [hk, Nat.cast_zero, zero_add] at hh
  exact (lt_div_iff₀ (by exact_mod_cast (show 0 < m by omega))).mpr hh

theorem count_exponent_comparison (θ ε : ℝ) (hθ : θ < 1)
    (hε : 0 ≤ ε ∧ ε ≤ (1-θ)/2) (m : ℕ) :
    Real.exp (-(m : ℝ)*(1-θ)^2/2) ≤ Real.exp (-2*(m : ℝ)*ε^2) := by
  apply Real.exp_le_exp.mpr
  have hsq : ε^2 ≤ ((1-θ)/2)^2 := pow_le_pow_left₀ hε.1 hε.2 2
  nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (α := ℝ) m)]

#print axioms indicator_trim_replacement
#print axioms zero_retained_shortcut
end NLA.IE21.LiteralWrappers
