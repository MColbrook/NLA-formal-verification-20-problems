module

public import NLA.MD06.CanonicalDisjointTuples.TupleCounts
public import NLA.MD06.CycleMoments.FirstLimits

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalDisjointTuples
open Reference.MD06SupportedCanonicalCycles Reference.MD06CycleMoments
open Reference.MD06PairingCounts Reference.MD06FiniteProbability
open Filter Topology
attribute [local instance] Classical.propDecidable

theorem actual_canonical_scaled_formula_limit (w : ℕ) :
    Tendsto (fun n : ℕ => ((n.descFactorial w*6^w : ℕ) : ℝ)/
      (PairingDenominator n w : ℝ)) atTop (𝓝 ((2 : ℝ)^w)) := by
  have ht := (actual_normalized_desc_factorial_limit w).div
    (actual_normalized_pairing_denominator_limit w) (by positivity)
  have hm := ht.mul_const ((6 : ℝ)^w)
  have hc : (1/(3 : ℝ)^w)*(6 : ℝ)^w=(2 : ℝ)^w := by
    rw [one_div_mul_eq_div,←div_pow]
    norm_num
  rw [hc] at hm
  apply hm.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (by omega : n≠0)
  simp only [Pi.div_apply,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  field_simp [hn0]

theorem actual_mean_canonical_disjoint_tuple_limit {q : ℕ}
    (L : Fin q→ℕ) (hL : ∀i,0<L i) :
    Tendsto (fun k => MeanTuple (Size k) L) atTop
      (𝓝 ((2 : ℝ)^(CycleWeight L)/(CycleSymmetryFactor L : ℝ))) := by
  have hs : Tendsto Size atTop atTop := by
    apply tendsto_atTop.2
    intro a
    filter_upwards [eventually_ge_atTop a] with k hk
    simp only [Size]
    omega
  have ht := ((actual_canonical_scaled_formula_limit (CycleWeight L)).comp hs).div_const
    (CycleSymmetryFactor L : ℝ)
  have hF : (CycleSymmetryFactor L : ℝ)≠0 := by
    exact_mod_cast (Nat.ne_of_gt (actual_cycle_symmetry_factor_positive L hL))
  apply ht.congr
  intro k
  dsimp only [Function.comp_apply]
  rw [←actual_mean_tuple_scaled_formula k L hL]
  field_simp [hF]

#print axioms actual_canonical_scaled_formula_limit
#print axioms actual_mean_canonical_disjoint_tuple_limit
end Reference.MD06CanonicalDisjointTuples
