module

public import NLA.MF05.PaperGrowthDefinitions
public import NLA.MF05.PaperNilpotence
public import NLA.MF07.Numerical
public import NLA.MF07.ScalarFamily

@[expose] public section

set_option autoImplicit false
open NLA.MF07
noncomputable section
namespace NLA.MF05.Paper

lemma binomial_bound_exp (m n : ℕ) (hn : 1 ≤ n) :
    (1 + (m : ℝ)/(n : ℝ))^n ≤ (Real.exp 1)^m := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hb : 1 + (m : ℝ)/(n : ℝ) ≤ Real.exp ((m : ℝ)/(n : ℝ)) := by
    simpa only [add_comm] using Real.add_one_le_exp ((m : ℝ)/(n : ℝ))
  calc
    _ ≤ (Real.exp ((m : ℝ)/(n : ℝ)))^n :=
      pow_le_pow_left₀ (by positivity) hb n
    _ = Real.exp (m : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    _ = (Real.exp 1)^m := by simpa using Real.exp_nat_mul 1 m

theorem sharp_threshold_bound (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (L : ℝ) (hL : 1 ≤ L) :
    (d : ℝ) * comparisonThreshold d n L^(d-1) *
      (1 + ((d-1 : ℕ) : ℝ)/(n : ℝ))^n ≤ theta d * (L*(n : ℝ))^(d-1) := by
  have hs := comparisonThreshold_ge_one d n hd hn L hL
  calc
    _ ≤ (d : ℝ) * comparisonThreshold d n L^(d-1) * (Real.exp 1)^(d-1) :=
      mul_le_mul_of_nonneg_left (binomial_bound_exp (d-1) n hn)
        (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg (by linarith) _))
    _ = _ := by
      rw [theta, if_neg (by omega)]
      unfold comparisonThreshold
      rw [mul_assoc, ← mul_pow]
      have hid : 2*(d : ℝ)^2*L*(n : ℝ)/((d-1 : ℕ) : ℝ)*Real.exp 1 =
          (2*Real.exp 1*(d : ℝ)^2/((d-1 : ℕ) : ℝ))*(L*(n : ℝ)) := by ring
      rw [hid, mul_pow]
      ring

theorem complex_positive_radius_growth_quotient {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L)
    (hr : 0 < jointSpectralRadius M) (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) *
      (jointSpectralRadius M)^n/(jointSpectralRadius M)^(d-1) := by
  by_cases hd1 : d = 1
  · subst d
    obtain ⟨hg, he⟩ := scalar_family_growth M hM hne
    simp [theta, hg n, he]
  have hd2 : 2 ≤ d := by omega
  let r := jointSpectralRadius M
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hrL : r ≤ L := (jointSpectralRadius_bounds_of_inNormBall hd M hM hne L hML).2
  have hLr : 1 ≤ L/r := (one_le_div hr).mpr hrL
  let s := comparisonThreshold d n (L/r)
  have hs : 1 ≤ s := comparisonThreshold_ge_one d n hd2 hn (L/r) hLr
  have hs0 : s ≠ 0 := by linarith
  have hratio : 2*(d : ℝ)^2*L/s = r*(((d-1 : ℕ) : ℝ)/(n : ℝ)) := by
    have h := comparisonThreshold_ratio d n hd2 hn (L/r) hLr
    change 2*(d : ℝ)^2*(L/r)/s = _ at h
    calc
      _ = r*(2*(d : ℝ)^2*(L/r)/s) := by field_simp
      _ = _ := by rw [h]
  have hbound := general_quantitative_comparison hd M hM hne L s hL hML hs n
  have hrate : comparisonRate d M L s = r*(1+((d-1 : ℕ) : ℝ)/(n : ℝ)) := by
    change r + 2*(d : ℝ)^2*L/s = _
    rw [hratio]
    ring
  rw [hrate, mul_pow] at hbound
  have hnumb := sharp_threshold_bound d n hd2 hn (L/r) hLr
  have h := mul_le_mul_of_nonneg_right hnumb (pow_nonneg hr.le n)
  calc
    familyGrowth M n ≤ ((d : ℝ)*s^(d-1)*
        (1+((d-1 : ℕ) : ℝ)/(n : ℝ))^n)*r^n := by
      simpa only [comparisonFactor, mul_assoc, mul_left_comm, mul_comm] using hbound
    _ ≤ theta d*((L/r)*(n : ℝ))^(d-1)*r^n := h
    _ = _ := by
      rw [show (L/r)*(n : ℝ) = (L*(n : ℝ))/r by ring, div_pow]
      ring

theorem complex_positive_radius_growth {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L)
    (hr : 0 < jointSpectralRadius M) (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) *
      (jointSpectralRadius M)^((n : ℤ)-(d : ℤ)+1) := by
  have he : (n : ℤ)-(d : ℤ)+1 = (n : ℤ)-((d-1 : ℕ) : ℤ) := by omega
  rw [he, zpow_sub₀ (ne_of_gt hr), zpow_natCast, zpow_natCast]
  simpa only [mul_div_assoc] using
    complex_positive_radius_growth_quotient hd M hM hne L hL hML hr n hn

#print axioms complex_positive_radius_growth
end NLA.MF05.Paper
