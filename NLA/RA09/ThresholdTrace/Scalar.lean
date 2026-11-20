module

public import NLA.RA09.ThresholdTrace.Definitions
public import NLA.RA09.Paper.UnorderedMatrix

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace RootRA09ThresholdTrace
open NLA.RA09

theorem actual_squared_difference (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ x y : ℝ) (hτ : 0 < τ) (htx : τ ≤ x) (hxy : x ≤ y) :
    (f y)^2-(f x)^2 ≤ (transferScale f τ)^2*(y^2-x^2) := by
  obtain ⟨_,hc,_,hhi,hlip,_⟩ := Paper.admissible_scalar_consequences_proved f hf τ hτ
  have hx : 0 ≤ x := hτ.le.trans htx
  have hy : 0 ≤ y := hx.trans hxy
  have hd := hlip x y hx hxy (htx.trans hxy)
  have hs : f y+f x ≤ transferScale f τ*(y+x) := by
    have h1 := hhi x htx
    have h2 := hhi y (htx.trans hxy)
    nlinarith
  have hm := mul_le_mul hd.2 hs (add_nonneg (hf.2.2.1 y hy) (hf.2.2.1 x hx))
    (mul_nonneg hc (sub_nonneg.mpr hxy))
  nlinarith [hm]

theorem above_monotone (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) :
    MonotoneOn (fun a => 2*(transferScale f τ)^2*a^2-(f a)^2) (Set.Ici τ) := by
  intro x hx y hy hxy
  have hs := actual_squared_difference f hf τ x y hτ hx hxy
  have hsq : 0 ≤ y^2-x^2 := sub_nonneg.mpr (pow_le_pow_left₀ (hτ.le.trans hx) hxy 2)
  nlinarith [mul_nonneg (sq_nonneg (transferScale f τ)) hsq]

theorem actual_threshold_scalar (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) :
    (∀ a : ℝ, 0 ≤ a → a ≤ τ → thresholdAuxiliary f τ a = (f τ)^2) ∧
      (∀ a : ℝ, τ ≤ a → thresholdAuxiliary f τ a = 2*(transferScale f τ)^2*a^2-(f a)^2) ∧
      thresholdAuxiliary f τ τ = (f τ)^2 ∧
      MonotoneOn (thresholdAuxiliary f τ) (Set.Ici 0) := by
  have hcut := Paper.unordered_auxiliary_cutoff f hf τ hτ
  change (∀ a : ℝ, 0 ≤ a → a ≤ τ → thresholdAuxiliary f τ a = (f τ)^2) ∧
    (∀ a : ℝ, τ ≤ a → thresholdAuxiliary f τ a = 2*(transferScale f τ)^2*a^2-(f a)^2) at hcut
  refine ⟨hcut.1,hcut.2,hcut.1 τ hτ.le le_rfl,?_⟩
  intro x hx y hy hxy
  by_cases hyt : y ≤ τ
  · rw [hcut.1 x hx (hxy.trans hyt),hcut.1 y hy hyt]
  · by_cases hxt : x ≤ τ
    · rw [hcut.1 x hx hxt]
      exact le_max_right _ _
    · rw [hcut.2 x (lt_of_not_ge hxt).le,hcut.2 y (lt_of_not_ge hyt).le]
      exact above_monotone f hf τ hτ (lt_of_not_ge hxt).le (lt_of_not_ge hyt).le hxy

theorem actual_ordered_threshold_values {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (τ : ℝ) (hτ : 0 < τ) :
    Antitone (fun i => thresholdAuxiliary f τ (d.eigenvalues i)) := by
  intro i j hij
  exact (actual_threshold_scalar f hf τ hτ).2.2.2 (d.nonnegative j) (d.nonnegative i) (d.decreasing hij)

#print axioms actual_squared_difference
#print axioms actual_threshold_scalar
end RootRA09ThresholdTrace
