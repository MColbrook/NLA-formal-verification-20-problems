module

public import NLA.RA02.PaperPathNormalizers
public import NLA.RA02.PaperNormalizers
public import NLA.RA02.PaperSurvivalCount

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace NLA.RA02.Paper

theorem cholesky_history_product_limit {r : ℕ} (h : Fin r ↪ Fin (r+1)) :
    Tendsto (fun t : ℝ => ∏ s : Fin r, epsilon (r+1) t^s.val /
      historyTraceNormalizer (sharpFamily (r+1) t) h s) (𝓝[>] 0) (𝓝 (historyIndicator h)) := by
  unfold historyIndicator
  apply tendsto_finsetProd
  intro s _
  exact trace_indicator_limit (show s.val < r+1 by omega) (historyPrefix h s.isLt.le)

theorem lu_history_product_limit {r : ℕ} (rows cols : Fin r ↪ Fin (r+1)) :
    Tendsto (fun t : ℝ => ∏ s : Fin r, epsilon (r+1) t^(2*s.val) /
      historyFrobeniusNormalizer (sharpFamily (r+1) t) rows cols s)
      (𝓝[>] 0) (𝓝 (historyIndicator rows * historyIndicator cols)) := by
  unfold historyIndicator
  rw [← Finset.prod_mul_distrib]
  apply tendsto_finsetProd
  intro s _
  exact frobenius_indicator_limit (show s.val < r+1 by omega)
    (historyPrefix rows s.isLt.le) (historyPrefix cols s.isLt.le)

theorem cholesky_history_sum_limit (r : ℕ) :
    Tendsto (fun t : ℝ => ∑ h : Fin r ↪ Fin (r+1), ∏ s : Fin r,
      epsilon (r+1) t^s.val / historyTraceNormalizer (sharpFamily (r+1) t) h s)
      (𝓝[>] 0) (𝓝 ((2 : ℝ)^r)) := by
  have hh := tendsto_finsetSum Finset.univ (fun (h : Fin r ↪ Fin (r+1)) _ => cholesky_history_product_limit h)
  rw [history_indicator_sum] at hh
  exact hh

theorem lu_history_sum_limit (r : ℕ) :
    Tendsto (fun t : ℝ => ∑ rows : Fin r ↪ Fin (r+1), ∑ cols : Fin r ↪ Fin (r+1),
      ∏ s : Fin r, epsilon (r+1) t^(2*s.val) /
        historyFrobeniusNormalizer (sharpFamily (r+1) t) rows cols s)
      (𝓝[>] 0) (𝓝 ((4 : ℝ)^r)) := by
  have hh := tendsto_finsetSum Finset.univ (fun (rows : Fin r ↪ Fin (r+1)) _ =>
    tendsto_finsetSum Finset.univ (fun (cols : Fin r ↪ Fin (r+1)) _ => lu_history_product_limit rows cols))
  rw [history_pair_indicator_sum] at hh
  exact hh

theorem product_scaled_normalizers (r : ℕ) (e : ℝ) (f : Fin r → ℝ) :
    (∏ s : Fin r, e^s.val / f s) = e^(r*(r-1)/2) * ∏ s : Fin r, 1 / f s := by
  simp only [div_eq_mul_inv, one_mul, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id]

theorem sharpFamily_allMinors (n : ℕ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, AllSquareMinorsNonzero (sharpFamily n t) := by
  filter_upwards [all_minors_eventually_nonzero n] with t ht
  intro s hs rows cols
  exact ht ⟨s,by omega⟩ rows cols

theorem sharp_cholesky_scaled_identity (r : ℕ) {t : ℝ} (ht : 0 < t)
    (ha : AllSquareMinorsNonzero (sharpFamily (r+1) t)) :
    NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) t)) r / epsilon (r+1) t^r =
      ∑ h : Fin r ↪ Fin (r+1), ∏ s : Fin r,
        epsilon (r+1) t^s.val / historyTraceNormalizer (sharpFamily (r+1) t) h s := by
  rw [real_cholesky_history_identity _ ha (sharpFamily_posDef _ _ ht).posSemidef, sharpFamily_det,
    triangular_exponent_succ]
  simp_rw [product_scaled_normalizers]
  rw [← Finset.mul_sum, pow_add]
  have he : epsilon (r+1) t ≠ 0 := pow_ne_zero _ (ne_of_gt ht)
  field_simp
  <;> ring

theorem sharp_lu_scaled_identity (r : ℕ) {t : ℝ} (ht : 0 < t)
    (ha : AllSquareMinorsNonzero (sharpFamily (r+1) t)) :
    NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r / epsilon (r+1) t^(2*r) =
      ∑ rows : Fin r ↪ Fin (r+1), ∑ cols : Fin r ↪ Fin (r+1), ∏ s : Fin r,
        epsilon (r+1) t^(2*s.val) / historyFrobeniusNormalizer (sharpFamily (r+1) t) rows cols s := by
  rw [real_lu_history_identity _ ha, sq_abs, sharpFamily_det, triangular_exponent_succ]
  simp_rw [pow_mul, product_scaled_normalizers]
  simp_rw [← Finset.mul_sum]
  rw [pow_add, mul_pow]
  have he : epsilon (r+1) t ≠ 0 := pow_ne_zero _ (ne_of_gt ht)
  rw [pow_right_comm (epsilon (r+1) t) (r*(r-1)/2) 2, pow_right_comm (epsilon (r+1) t) r 2]
  field_simp
  <;> ring

theorem sharp_cholesky_epsilon_limit (r : ℕ) :
    Tendsto (fun t : ℝ => NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) t)) r /
      epsilon (r+1) t^r) (𝓝[>] 0) (𝓝 ((2 : ℝ)^r)) := by
  apply (cholesky_history_sum_limit r).congr'
  filter_upwards [sharpFamily_allMinors (r+1), self_mem_nhdsWithin] with t ha ht
  exact (sharp_cholesky_scaled_identity r ht ha).symm

theorem sharp_lu_epsilon_limit (r : ℕ) :
    Tendsto (fun t : ℝ => NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r /
      epsilon (r+1) t^(2*r)) (𝓝[>] 0) (𝓝 ((4 : ℝ)^r)) := by
  apply (lu_history_sum_limit r).congr'
  filter_upwards [sharpFamily_allMinors (r+1), self_mem_nhdsWithin] with t ha ht
  exact (sharp_lu_scaled_identity r ht ha).symm

#print axioms sharp_lu_epsilon_limit
end NLA.RA02.Paper
