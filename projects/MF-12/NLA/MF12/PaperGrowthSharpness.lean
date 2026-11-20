module

public import NLA.MF12.JordanBounds
public import NLA.MF12.RootLimit
public import Mathlib.Analysis.SpecialFunctions.Choose

@[expose] public section

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace NLA.MF12.Paper

theorem jordan_top_right (m n : ℕ) :
    (jordanMatrix m ^ n) (0 : Fin (m+1)) ⟨m, by omega⟩ = (n.choose m : ℝ) := by
  simp [jordan_entries]

theorem jordan_top_right_asymptotic (m : ℕ) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (jordanMatrix m ^ n) (0 : Fin (m+1)) ⟨m, by omega⟩)
      (fun n : ℕ => (n : ℝ)^m / (m.factorial : ℝ)) := by
  simpa only [jordan_top_right] using isEquivalent_choose m

theorem jordan_root_limit (m : ℕ) :
    Tendsto (fun n : ℕ => Real.rpow (spectralNorm (jordanMatrix m ^ n)) (1/(n : ℝ)))
      atTop (𝓝 1) := by
  apply roots_of_polynomial_growth _ (m : ℝ) (jordanLower m) (m+1)
    (Nat.cast_nonneg m) (jordanLower_pos m) (by positivity)
  intro n hn
  simpa only [Real.rpow_eq_pow, Real.rpow_natCast, Nat.cast_add, Nat.cast_one] using
    (jordan_growth_estimates m).2.2 n hn

theorem jordan_no_smaller_exponent (m : ℕ) (β C : ℝ) (hβ : β < (m : ℝ))
    (N : ℕ) :
    ∃ n : ℕ, max 1 N ≤ n ∧ C * Real.rpow (n : ℝ) β < spectralNorm (jordanMatrix m ^ n) := by
  have ht : Tendsto (fun n : ℕ => Real.rpow (n : ℝ) ((m : ℝ)-β)) atTop atTop :=
    by
      have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      simpa only [Function.comp_def, Real.rpow_eq_pow] using
        (_root_.tendsto_rpow_atTop (sub_pos.mpr hβ)).comp hnat
  obtain ⟨n, hlarge, hn⟩ := ((ht.eventually (eventually_gt_atTop (C/jordanLower m))).and
    (eventually_ge_atTop (max 1 N))).exists
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc := jordanLower_pos m
  have hb := Real.rpow_pos_of_pos hnR β
  simp only [Real.rpow_eq_pow] at hlarge ⊢
  rw [Real.rpow_sub hnR, Real.rpow_natCast] at hlarge
  have hh := mul_lt_mul_of_pos_left ((lt_div_iff₀ hb).mp hlarge) hc
  have he : jordanLower m * (C / jordanLower m * Real.rpow (n : ℝ) β) =
      C * Real.rpow (n : ℝ) β := by field_simp
  simp only [Real.rpow_eq_pow] at he
  rw [he] at hh
  exact ⟨n, hn, hh.trans_le (jordan_norm_lower m n)⟩

#print axioms jordan_top_right
#print axioms jordan_top_right_asymptotic
#print axioms jordan_root_limit
#print axioms jordan_no_smaller_exponent

end NLA.MF12.Paper
