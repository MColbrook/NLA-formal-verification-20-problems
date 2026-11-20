module

public import NLA.MD06.BoundedExcessPatterns.ConditioningDefinitions
public import NLA.MD06.BoundedExcessPatterns.InverseBounds
public import NLA.MD06.CombinedZeroProbability.Conditioning

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06BoundedExcess
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open Reference.MD06CombinedZero
open Filter Topology
attribute [local instance] Classical.propDecidable

theorem actual_pairing_probability_mono {n : ℕ} (P Q : Pairing n→Prop)
    (h : ∀p,P p→Q p) : PairingProbability n P≤PairingProbability n Q := by
  let f : {p : Pairing n // P p}→{p : Pairing n // Q p} := fun p => ⟨p.val,h p.val p.property⟩
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    exact congrArg (fun z : {p : Pairing n // Q p} => z.val) he
  unfold PairingProbability
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Fintype.card_le_of_injective f hf

theorem actual_simple_excess_numerator_nonnegative (k K : ℕ) :
    0≤SimpleExcessNumerator k K := by
  unfold SimpleExcessNumerator PairingProbability
  positivity

theorem actual_simple_excess_numerator_le (k K : ℕ) :
    SimpleExcessNumerator k K≤ExcessProbability k K :=
  actual_pairing_probability_mono _ _ (fun _ h => h.2)

theorem actual_simple_excess_numerator_limit (K : ℕ) :
    Tendsto (fun k => SimpleExcessNumerator k K) atTop (𝓝 0) :=
  squeeze_zero (fun k => actual_simple_excess_numerator_nonnegative k K)
    (fun k => actual_simple_excess_numerator_le k K) (actual_bounded_excess_probability_limit K)

theorem actual_simple_excess_probability_limit (K : ℕ) :
    Tendsto (fun k => SimpleExcessProbability k K) atTop (𝓝 0) := by
  have h := (actual_simple_excess_numerator_limit K).div
    actual_simple_pairing_probability_limit (Real.exp_ne_zero (-2))
  have he : (fun k => SimpleExcessNumerator k K)/(fun k => PairingProbability (Size k) IsSimplePairing)=
      (fun k => SimpleExcessProbability k K) := by
    funext k
    rfl
  rw [he] at h
  simpa only [zero_div] using h

theorem actual_simple_excess_inverse_size_bound (K : ℕ) :
    ∀ᶠk : ℕ in atTop,
      SimpleExcessProbability k K≤(2*BoundConstant K/Real.exp (-2))/(Size k : ℝ) := by
  have hpos : 0<Real.exp (-2)/2 := by positivity
  have hsmall : Real.exp (-2)/2<Real.exp (-2) := by linarith [Real.exp_pos (-2)]
  have hp := actual_simple_pairing_probability_limit.eventually (eventually_gt_nhds hsmall)
  filter_upwards [hp,actual_bounded_excess_inverse_size_bound K] with k hk hb
  have hn : 0<(Size k : ℝ) := by exact_mod_cast (show 0<Size k from by unfold Size;omega)
  have hp0 : 0<PairingProbability (Size k) IsSimplePairing := hpos.trans hk
  have hx : SimpleExcessNumerator k K≤BoundConstant K/(Size k : ℝ) :=
    (actual_simple_excess_numerator_le k K).trans hb
  unfold SimpleExcessProbability
  calc
    SimpleExcessNumerator k K/PairingProbability (Size k) IsSimplePairing≤
        (BoundConstant K/(Size k : ℝ))/PairingProbability (Size k) IsSimplePairing :=
      div_le_div_of_nonneg_right hx hp0.le
    _ ≤ (BoundConstant K/(Size k : ℝ))/(Real.exp (-2)/2) :=
      div_le_div_of_nonneg_left (div_nonneg (actual_bound_constant_nonnegative K) hn.le) hpos hk.le
    _ = _ := by ring

#print axioms actual_pairing_probability_mono
#print axioms actual_simple_excess_numerator_nonnegative
#print axioms actual_simple_excess_numerator_le
#print axioms actual_simple_excess_numerator_limit
#print axioms actual_simple_excess_probability_limit
#print axioms actual_simple_excess_inverse_size_bound
end Reference.MD06BoundedExcess
