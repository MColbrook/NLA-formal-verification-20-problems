module

public import NLA.MD06.CombinedZeroProbability.ConditioningDefinitions
public import NLA.MD06.CombinedZeroProbability.ExpLimits
public import NLA.MD06.MixedLowCycleBijections.MarkedBinding
public import NLA.MD06.CubicConfiguration.PairingMeasure

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedZero
open Reference.MD06MixedLowCycleBijections Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06Simplicity
open Filter Topology
attribute [local instance] Classical.propDecidable

theorem actual_combined_zero_iff {n ell : ℕ} (p : Pairing n) :
    MarkedMatchingCount (ell:=ell) p=0 ↔
      IsSimplePairing p ∧ CanonicalCycleCount n ell p=0 := by
  rw [actual_marked_matching_count_sum,Nat.add_eq_zero_iff,←actual_simple_pairing_iff_bad_count_zero]

theorem actual_zero_probability_simple_cycle_binding (k ell : ℕ) :
    ZeroProbability k ell=PairingProbability (Size k)
      (fun p => IsSimplePairing p ∧ CanonicalCycleCount (Size k) ell p=0) := by
  have h : (fun p : Pairing (Size k) => MarkedMatchingCount (ell:=ell) p=0)=
      (fun p => IsSimplePairing p ∧ CanonicalCycleCount (Size k) ell p=0) := by
    funext p
    exact propext (actual_combined_zero_iff p)
  unfold ZeroProbability
  rw [h]

theorem actual_simple_pairing_probability_limit :
    Tendsto (fun k => PairingProbability (Size k) IsSimplePairing) atTop
      (𝓝 (Real.exp (-2))) := by
  have h (k : ℕ) : PairingProbability (Size k) IsSimplePairing=
      Reference.MD06SimplicityExponential.SimpleProbability k := by
    unfold Reference.MD06SimplicityExponential.SimpleProbability
    rw [actual_pairing_probability_uniform_real]
  simpa only [h] using
    Reference.MD06SimplicityExponential.actual_simple_pairing_probability_exponential_limit

theorem actual_simple_conditioned_no_cycle_limit (ell : ℕ) (hell : 3≤ell) :
    Tendsto (fun k => SimpleNoCycleProbability k ell) atTop
      (𝓝 (Real.exp (-((2 : ℝ)^ell/(2*(ell : ℝ)))))) := by
  have h := (actual_combined_zero_probability_limit ell hell).div
    actual_simple_pairing_probability_limit (Real.exp_ne_zero (-2))
  have hx : Real.exp (-(2+(2 : ℝ)^ell/(2*(ell : ℝ))))/Real.exp (-2)=
      Real.exp (-((2 : ℝ)^ell/(2*(ell : ℝ)))) := by
    rw [←Real.exp_sub]
    congr 1
    ring
  rw [hx] at h
  have he : (fun k => ZeroProbability k ell)/(fun k => PairingProbability (Size k) IsSimplePairing)=
      (fun k => SimpleNoCycleProbability k ell) := by
    funext k
    change ZeroProbability k ell/PairingProbability (Size k) IsSimplePairing=SimpleNoCycleProbability k ell
    rw [actual_zero_probability_simple_cycle_binding]
    rfl
  rw [he] at h
  exact h

#print axioms actual_combined_zero_iff
#print axioms actual_zero_probability_simple_cycle_binding
#print axioms actual_simple_pairing_probability_limit
#print axioms actual_simple_conditioned_no_cycle_limit
end Reference.MD06CombinedZero
