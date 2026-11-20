module

public import NLA.MD06.SimplicityBonferroni.Simplicity
public import NLA.MD06.CubicConfiguration.PairingMeasure
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Simplicity
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_simple_indicator_sum {n : ℕ} :
    (∑ p : Pairing n, if IsSimplePairing p then (1 : ℝ) else 0) =
      (Fintype.card {p : Pairing n // IsSimplePairing p} : ℝ) := by
  rw [Fintype.card_subtype]
  simp

theorem actual_simple_probability_bonferroni_seven (k : ℕ) :
    (∑ i ∈ Finset.range 8, (-1 : ℝ)^i *
      ((∑ p : Pairing (Size k), ((BadCount p).choose i : ℝ)) /
        (Fintype.card (Pairing (Size k)) : ℝ))) ≤
      ((UniformPairing k).toOuterMeasure {p | IsSimplePairing p}).toReal := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Pairing (Size k))))
    (fun p _ => actual_simple_indicator_bonferroni_seven p)
  calc
    _ = (∑ i ∈ Finset.range 8, ∑ p : Pairing (Size k),
        (-1 : ℝ)^i * ((BadCount p).choose i : ℝ)) /
          (Fintype.card (Pairing (Size k)) : ℝ) := by
      simp_rw [← mul_div_assoc,Finset.mul_sum]
      rw [← Finset.sum_div]
    _ = (∑ p : Pairing (Size k), ∑ i ∈ Finset.range 8,
        (-1 : ℝ)^i * ((BadCount p).choose i : ℝ)) /
          (Fintype.card (Pairing (Size k)) : ℝ) := by
      rw [Finset.sum_comm]
    _ ≤ (∑ p : Pairing (Size k), if IsSimplePairing p then (1 : ℝ) else 0) /
          (Fintype.card (Pairing (Size k)) : ℝ) :=
      div_le_div_of_nonneg_right h (Nat.cast_nonneg _)
    _ = _ := by
      rw [actual_simple_indicator_sum,actual_pairing_probability_uniform_real]
      simp only [PairingProbability,← Nat.card_eq_fintype_card]

#print axioms actual_simple_indicator_sum
#print axioms actual_simple_probability_bonferroni_seven
end Reference.MD06Simplicity