module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Topology
open Filter
namespace NLA.RA02.Paper

theorem lowerSemicontinuousAt_nonneg_zero {α : Type*} [TopologicalSpace α]
    (f : α → ℝ) (a : α) (hf : ∀ x, 0 ≤ f x) (ha : f a = 0) :
    LowerSemicontinuousAt f a := by
  intro y hy
  rw [ha] at hy
  exact Eventually.of_forall (fun x => hy.trans_le (hf x))

theorem lowerSemicontinuousAt_mul_nonneg {α : Type*} [TopologicalSpace α]
    (f g : α → ℝ) (a : α) (hf : ContinuousAt f a) (hg : LowerSemicontinuousAt g a)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) :
    LowerSemicontinuousAt (fun x => f x*g x) a := by
  by_cases hfa : f a = 0
  · exact lowerSemicontinuousAt_nonneg_zero _ a
      (fun x => mul_nonneg (hfn x) (hgn x)) (by rw [hfa,zero_mul])
  have hfp : 0 < f a := lt_of_le_of_ne (hfn a) (Ne.symm hfa)
  intro y hy
  by_cases hyn : y < 0
  · exact Eventually.of_forall (fun x => hyn.trans_le (mul_nonneg (hfn x) (hgn x)))
  have hyd : y/f a < g a := (div_lt_iff₀ hfp).mpr (by nlinarith)
  obtain ⟨z,hyz,hzg⟩ := exists_between hyd
  have hz : 0 ≤ z := (div_nonneg (le_of_not_gt hyn) hfp.le).trans hyz.le
  have hyprod : y < f a*z := by
    have he := (div_lt_iff₀ hfp).mp hyz
    nlinarith
  have hc : ContinuousAt (fun x => f x*z) a := hf.mul continuousAt_const
  have he : ∀ᶠ x in 𝓝 a, y < f x*z := hc.eventually (eventually_gt_nhds hyprod)
  filter_upwards [he,hg z hzg] with x hx hxg
  exact hx.trans_le (mul_le_mul_of_nonneg_left hxg.le (hfn x))

#print axioms lowerSemicontinuousAt_mul_nonneg
end NLA.RA02.Paper
