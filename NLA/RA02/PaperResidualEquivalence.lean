module

public import NLA.RA02.PaperResidualEntry
public import NLA.RA02.PaperResidualZeros
public import NLA.RA02.PaperInterpolationEquations
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter Asymptotics
namespace NLA.RA02.Paper

theorem finset_sum_equiv_nonneg {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (a b : ι → ℝ → ℝ) (ha : ∀ i, a i ~[𝓝[>] 0] b i) (hb : ∀ i t, 0 ≤ b i t) :
    (fun t => ∑ i ∈ S, a i t) ~[𝓝[>] 0] (fun t => ∑ i ∈ S, b i t) := by
  induction S using Finset.induction_on with
  | empty => simpa using (IsEquivalent.refl (u := (fun _ : ℝ => (0 : ℝ))) (l := 𝓝[>] (0 : ℝ)))
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    change (a i + fun t => ∑ j ∈ S, a j t) ~[𝓝[>] 0] (b i + fun t => ∑ j ∈ S, b j t)
    exact IsEquivalent.add_add_of_nonneg (hb i)
      (fun t => Finset.sum_nonneg (fun j _ => hb j t)) (ha i) ih

theorem residual_entry_equivalent {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n) (i j : Fin n) :
    (fun t => interpolatoryResidual (sharpFamily n t) rows cols i j / epsilon n t^s)
      ~[𝓝[>] 0] (fun t => interpolationResidual hs rows t i * interpolationResidual hs cols t j) := by
  by_cases hi : i ∈ Set.range rows
  · obtain ⟨k,rfl⟩ := hi
    apply Filter.EventuallyEq.isEquivalent
    filter_upwards [spectral_minor_eventually_nonzero hs.le rows cols,
      prefix_eventually_nonsingular hs.le rows] with t ha hp
    have hau := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ha)
    have hpu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp)
    rw [residual_selected_row _ rows cols hau k j,
      interpolation_vanishes_on_rows hs rows t hpu k, zero_div, zero_mul]
  · by_cases hj : j ∈ Set.range cols
    · obtain ⟨k,rfl⟩ := hj
      apply Filter.EventuallyEq.isEquivalent
      filter_upwards [spectral_minor_eventually_nonzero hs.le rows cols,
        prefix_eventually_nonsingular hs.le cols] with t ha hp
      have hau := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ha)
      have hpu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hp)
      rw [residual_selected_column _ rows cols hau i k,
        interpolation_vanishes_on_rows hs cols t hpu k, zero_div, mul_zero]
    · apply isEquivalent_of_tendsto_one
      change Tendsto (fun t => (interpolatoryResidual (sharpFamily n t) rows cols i j / epsilon n t^s) /
        (interpolationResidual hs rows t i * interpolationResidual hs cols t j)) _ _
      simpa only [div_div, mul_assoc] using residual_entry_ratio hs rows cols i j hi hj

theorem trace_equivalent {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    (fun t => paperTrace rows t / epsilon n t^s) ~[𝓝[>] 0] interpolationSquaredNorm hs rows := by
  have he : ∀ i : Fin n,
      (fun t => interpolatoryResidual (sharpFamily n t) rows rows i i / epsilon n t^s)
        ~[𝓝[>] 0] (fun t => (interpolationResidual hs rows t i)^2) := by
    intro i
    simpa only [pow_two] using residual_entry_equivalent hs rows rows i i
  have hh := finset_sum_equiv_nonneg Finset.univ _ _ he (fun i t => sq_nonneg _)
  change (fun t => (∑ i, interpolatoryResidual (sharpFamily n t) rows rows i i) / epsilon n t^s)
    ~[𝓝[>] 0] (fun t => ∑ i, (interpolationResidual hs rows t i)^2)
  simpa only [Finset.sum_div] using hh

theorem frobenius_equivalent {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n) :
    (fun t => paperFrobeniusSquared rows cols t / epsilon n t^(2*s)) ~[𝓝[>] 0]
      (fun t => interpolationSquaredNorm hs rows t * interpolationSquaredNorm hs cols t) := by
  have he : ∀ i j : Fin n,
      (fun t => (interpolatoryResidual (sharpFamily n t) rows cols i j / epsilon n t^s)^2)
        ~[𝓝[>] 0] (fun t => (interpolationResidual hs rows t i)^2 * (interpolationResidual hs cols t j)^2) := by
    intro i j
    have hh := (residual_entry_equivalent hs rows cols i j).pow 2
    change (fun t => (interpolatoryResidual (sharpFamily n t) rows cols i j / epsilon n t^s)^2)
      ~[𝓝[>] 0] (fun t => (interpolationResidual hs rows t i * interpolationResidual hs cols t j)^2) at hh
    simpa only [mul_pow] using hh
  have hh := finset_sum_equiv_nonneg Finset.univ _ _
    (fun i => finset_sum_equiv_nonneg Finset.univ _ _ (he i)
      (fun j t => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    (fun i t => Finset.sum_nonneg (fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hp : ∀ t : ℝ, (epsilon n t^s)^2 = epsilon n t^(2*s) := by
    intro t
    rw [← pow_mul, Nat.mul_comm s 2]
  simpa only [paperFrobeniusSquared, div_pow, hp, Finset.sum_div, interpolationSquaredNorm,
    Finset.sum_mul_sum] using hh

#print axioms frobenius_equivalent
end NLA.RA02.Paper
