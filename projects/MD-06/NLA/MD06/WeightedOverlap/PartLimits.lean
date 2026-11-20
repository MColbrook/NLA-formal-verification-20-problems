module

public import NLA.MD06.WeightedOverlap.PartCounts

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WeightedOverlap
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
open Reference.MD06CycleMoments Reference.MD06FiniteProbability
open Filter Topology

theorem actual_excess_denominator_formula_limit (v e : ℕ) (hve : v < e) :
    Tendsto (fun n : ℕ => (n : ℝ)^v/(PairingDenominator n e : ℝ))
      atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hd : e-v ≠ 0 := by omega
  have hz : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)^(e-v)) atTop (𝓝 0) := by
    simpa only [zero_pow hd] using hi.pow (e-v)
  have h := hz.mul (actual_scaled_pattern_denominator_reciprocal_limit e)
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have he : e = v+(e-v) := by omega
  by_cases ht : (PairingDenominator n e : ℝ) = 0
  · simp [ht]
  · have hpow : (n : ℝ)^e = (n : ℝ)^v*(n : ℝ)^(e-v) := by
      calc
        (n : ℝ)^e = (n : ℝ)^(v+(e-v)) := congrArg (fun a => (n : ℝ)^a) he
        _ = (n : ℝ)^v*(n : ℝ)^(e-v) := pow_add _ _ _
    rw [hpow]
    field_simp [hn0,ht]
    rw [← mul_pow]
    simp [hn0]

theorem actual_size_tendsto_atTop : Tendsto Size atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  simp only [Size]
  omega

theorem actual_excess_part_mean_limit (q v e : ℕ) (hve : v < e) :
    Tendsto (fun k : ℕ => PartMean (Size k) q v e) atTop (𝓝 0) := by
  have h := (actual_excess_denominator_formula_limit v e hve).mul_const
    ((3*v+18*v^2 : ℕ)^q : ℝ)
  simp only [zero_mul] at h
  have hr : Tendsto (fun k : ℕ =>
      ((Size k : ℝ)^v*(3*v+18*v^2)^q)/(PairingDenominator (Size k) e : ℝ))
      atTop (𝓝 0) := by
    have hh := h.comp actual_size_tendsto_atTop
    convert hh using 1
    funext k
    simp only [Function.comp_apply,Nat.cast_pow,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat]
    ring
  exact squeeze_zero (fun k => actual_part_mean_nonnegative (Size k) q v e)
    (fun k => actual_part_mean_finite_bound k q v e) hr

theorem actual_part_mean_all_shapes_limit (q v e : ℕ) :
    Tendsto (fun k : ℕ => PartMean (Size k) q v e) atTop (𝓝 0) := by
  by_cases hve : v < e
  · exact actual_excess_part_mean_limit q v e hve
  · have hz (k : ℕ) : PartMean (Size k) q v e = 0 := by
      let : IsEmpty (PartDatum (Size k) q v e) :=
        ⟨fun f => hve (by have h := (actual_part_shape_bounds f).1;omega)⟩
      simp [PartMean,PartCount]
    simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

#print axioms actual_excess_denominator_formula_limit
#print axioms actual_size_tendsto_atTop
#print axioms actual_excess_part_mean_limit
#print axioms actual_part_mean_all_shapes_limit
end Reference.MD06WeightedOverlap
