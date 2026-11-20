module

public import NLA.IE22.VarianceTensorization
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace NLA.IE22.LipschitzPoincare

theorem coordinate_resampling_preserving (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ) (i : Fin d) :
    MeasurePreserving (fun z : (Fin d → ℝ) × ℝ => Function.update z.1 i z.2)
      ((Measure.pi (fun _ : Fin d => μ)).prod μ) (Measure.pi (fun _ : Fin d => μ)) := by
  classical
  let π : Measure (Fin d → ℝ) := Measure.pi (fun _ => μ)
  let U : ((Fin d → ℝ) × ℝ) → (Fin d → ℝ) := fun z => Function.update z.1 i z.2
  have hu : Measurable U := by
    apply Measurable.of_eval
    intro j
    by_cases h : j = i
    · subst j
      simpa [U] using measurable_snd
    · simpa [U, Function.update_of_ne h, Function.comp_def] using
        (measurable_pi_apply j).comp measurable_fst
  refine ⟨hu, ?_⟩
  change (π.prod μ).map U = π
  haveI : IsProbabilityMeasure ((π.prod μ).map U) := (Measure.isProbabilityMeasure_map_iff hu.aemeasurable).mpr inferInstance
  apply Measure.ext
  intro S hS
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((π.prod μ).map U).real S = π.real S
  rw [map_measureReal_apply hu hS]
  let F : (Fin d → ℝ) → ℝ := S.indicator (fun _ => 1)
  have hm : Measurable F := measurable_const.indicator hS
  have hb (x : Fin d → ℝ) : ‖F x‖ ≤ 1 := by
    by_cases h : x ∈ S <;> simp [F, h]
  have hi : Integrable (fun z => F (U z)) (π.prod μ) :=
    (MemLp.of_bound (hm.comp hu).aestronglyMeasurable 1
      (Eventually.of_forall fun z => hb (U z)) : MemLp (fun z => F (U z)) 2 (π.prod μ)).integrable (by norm_num)
  have he := bounded_integral_coordinate_resampling μ d F hm 1 hb i
  rw [← integral_prod _ hi] at he
  have heleft : (fun z => F (U z)) = (U ⁻¹' S).indicator (fun _ => (1 : ℝ)) := by
    funext z
    by_cases h : U z ∈ S <;> simp [F, h]
  change (∫ z, F (U z) ∂π.prod μ) = ∫ x, F x ∂π at he
  rw [heleft] at he
  simpa [F, integral_indicator (hS.preimage hu), integral_indicator hS] using he

#print axioms coordinate_resampling_preserving
end NLA.IE22.LipschitzPoincare
