module

public import NLA.MD06.CycleMoments.FirstLimits
public import NLA.MD06.PairingCounts.PatternProbability

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CycleMoments
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06FiniteProbability
open Filter Topology

theorem actual_scaled_pattern_denominator_reciprocal_limit (e : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^e / (PairingDenominator n e : ℝ))
      atTop (𝓝 (1/(3 : ℝ)^e)) := by
  have h := (actual_normalized_pairing_denominator_limit e).inv₀ (by positivity)
  simpa only [inv_div,one_div] using h

theorem actual_scaled_pattern_denominator_eventual_bound (e : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ)^e / (PairingDenominator n e : ℝ) ≤ 2/(3 : ℝ)^e := by
  have hc : (1 : ℝ)/(3 : ℝ)^e < 2/(3 : ℝ)^e := by
    exact div_lt_div_of_pos_right (by norm_num) (by positivity)
  have h := (actual_scaled_pattern_denominator_reciprocal_limit e).eventually
    (eventually_lt_nhds hc)
  exact h.mono (fun n hn => hn.le)

theorem actual_scaled_disjoint_pattern_probability_limit (e : ℕ)
    (C : (k : ℕ) → Finset (Dart (Size k) × Dart (Size k)))
    (hc : ∀ᶠ k : ℕ in atTop, (C k).card = e)
    (hd : ∀ᶠ k : ℕ in atTop, ∀ x ∈ C k, x.1 ≠ x.2)
    (hj : ∀ᶠ k : ℕ in atTop, ∀ x ∈ C k, ∀ y ∈ C k, x ≠ y →
      Disjoint ({x.1,x.2} : Finset (Dart (Size k))) {y.1,y.2}) :
    Tendsto (fun k : ℕ => (Size k : ℝ)^e *
      ((UniformPairing k).toOuterMeasure {p | Matches (C k) p}).toReal)
      atTop (𝓝 (1/(3 : ℝ)^e)) := by
  have hs : Tendsto Size atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    simp only [Size]
    omega
  apply ((actual_scaled_pattern_denominator_reciprocal_limit e).comp hs).congr'
  filter_upwards [hc,hd,hj] with k hck hdk hjk
  rw [actual_uniform_pairing_disjoint_pattern_probability k (C k) hdk hjk,hck]
  simp only [mul_one_div,Function.comp_apply]

theorem actual_uniform_disjoint_pattern_eventual_bound (e : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ C : Finset (Dart (Size k) × Dart (Size k)),
      C.card = e → (∀ x ∈ C, x.1 ≠ x.2) →
      (∀ x ∈ C, ∀ y ∈ C, x ≠ y →
        Disjoint ({x.1,x.2} : Finset (Dart (Size k))) {y.1,y.2}) →
      (Size k : ℝ)^e * ((UniformPairing k).toOuterMeasure {p | Matches C p}).toReal
        ≤ 2/(3 : ℝ)^e := by
  have hs : Tendsto Size atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    simp only [Size]
    omega
  have h := hs.eventually (actual_scaled_pattern_denominator_eventual_bound e)
  filter_upwards [h] with k hk
  intro C hc hd hj
  rw [actual_uniform_pairing_disjoint_pattern_probability k C hd hj,hc]
  simpa only [mul_one_div] using hk

#print axioms actual_scaled_pattern_denominator_reciprocal_limit
#print axioms actual_scaled_pattern_denominator_eventual_bound
#print axioms actual_scaled_disjoint_pattern_probability_limit
#print axioms actual_uniform_disjoint_pattern_eventual_bound
end Reference.MD06CycleMoments