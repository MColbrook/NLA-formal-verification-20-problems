module

public import NLA.IE22.LipschitzPoincare.Fibers

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace
namespace NLA.IE22.LipschitzPoincare
open NLA.IE21

/-- Gaussian Poincaré for bounded Lipschitz functions with the actual gradient.
The almost-everywhere full derivative is supplied by Rademacher's theorem. -/
theorem bounded_gaussian_poincare {d : ℕ} {C : ℝ≥0} {f : Space d → ℝ}
    (hf : LipschitzWith C f) (hbounded : ∃ B : ℝ, ∀ x, |f x| ≤ B) :
    Var[f; stdGaussian (Space d)] ≤ ∫ x, ‖gradient f x‖ ^ 2 ∂stdGaussian (Space d) := by
  let π : Measure (Fin d → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
  let φ : (Fin d → ℝ) → ℝ := fun x => f (WithLp.toLp 2 x)
  let H : Fin d → (Fin d → ℝ) → ℝ := fun i x => gradient f (WithLp.toLp 2 x) i ^ 2
  have htoLp : Measurable (WithLp.toLp 2 : (Fin d → ℝ) → Space d) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable
  have hφ : Measurable φ := hf.continuous.measurable.comp htoLp
  have hφb : ∃ B : ℝ, ∀ x, |φ x| ≤ B := by
    obtain ⟨B, hB⟩ := hbounded
    exact ⟨B, fun x => hB _⟩
  have hHm (i : Fin d) : Measurable (H i) := by
    dsimp [H]
    simp_rw [gradient_coordinate]
    exact ((measurable_fderiv_apply_const ℝ f _).comp htoLp).pow_const 2
  have hHb (i : Fin d) (x : Fin d → ℝ) : ‖H i x‖ ≤ (C : ℝ) ^ 2 := by
    have hh := (PiLp.norm_apply_le (gradient f (WithLp.toLp 2 x)) i).trans (gradient_norm_le hf _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
    simpa [H, Real.norm_eq_abs, sq_abs] using hs
  have hHi (i : Fin d) : Integrable (H i) π :=
    (MemLp.of_bound (hHm i).aestronglyMeasurable ((C : ℝ)^2)
      (Eventually.of_forall (hHb i)) : MemLp (H i) 2 π).integrable (by norm_num)
  have hdif : ∀ᵐ x ∂π, DifferentiableAt ℝ f (WithLp.toLp 2 x) := by
    have h := (gaussian_ae_gradient hf).mono fun _ hx => hx.differentiableAt
    rw [← map_pi_eq_stdGaussian] at h
    exact ae_of_ae_map htoLp.aemeasurable h
  have hcoordinate (i : Fin d) :
      (∫ x, Var[fun t => φ (Function.update x i t); gaussianReal 0 1] ∂π) ≤ ∫ x, H i x ∂π := by
    have hres := (coordinate_resampling_preserving (gaussianReal 0 1) d i).quasiMeasurePreserving.ae hdif
    have hsections := Measure.ae_ae_of_ae_prod hres
    have hUm : Measurable (fun z : (Fin d → ℝ) × ℝ => Function.update z.1 i z.2) :=
      (coordinate_resampling_preserving (gaussianReal 0 1) d i).measurable
    have hpair : Integrable (fun z : (Fin d → ℝ) × ℝ => H i (Function.update z.1 i z.2))
        (π.prod (gaussianReal 0 1)) :=
      (MemLp.of_bound ((hHm i).comp hUm).aestronglyMeasurable ((C : ℝ)^2)
        (Eventually.of_forall fun z => hHb i _) : MemLp _ 2 _).integrable (by norm_num)
    have hpoint : ∀ᵐ x ∂π,
        Var[fun t => φ (Function.update x i t); gaussianReal 0 1] ≤
          ∫ t, H i (Function.update x i t) ∂gaussianReal 0 1 := by
      filter_upwards [hsections] with x hx
      have hscalar := (scalar_gaussian_poincare (coordinate_fiber_lipschitz hf x i)).2.2.2
      have he : (∫ t, deriv (fun s => f (WithLp.toLp 2 (Function.update x i s))) t ^ 2
          ∂gaussianReal 0 1) = ∫ t, H i (Function.update x i t) ∂gaussianReal 0 1 := by
        apply integral_congr_ae
        filter_upwards [hx] with t ht
        rw [coordinate_fiber_derivative f x i t ht]
      exact he ▸ hscalar
    calc
      _ ≤ ∫ x, ∫ t, H i (Function.update x i t) ∂gaussianReal 0 1 ∂π :=
        integral_mono_ae (gaussian_coordinate_variance_integrable d φ hφ hφb i)
          hpair.integral_prod_left hpoint
      _ = _ := gaussian_integral_coordinate_resampling d (H i) (hHm i)
        ⟨(C : ℝ)^2, fun x => by simpa only [Real.norm_eq_abs] using hHb i x⟩ i
  calc
    _ = Var[φ; π] := by
      rw [← map_pi_eq_stdGaussian, variance_map hf.continuous.measurable.aemeasurable htoLp.aemeasurable]
      rfl
    _ ≤ ∑ i : Fin d, ∫ x, Var[fun t => φ (Function.update x i t); gaussianReal 0 1] ∂π :=
      gaussian_variance_tensorization d φ hφ hφb
    _ ≤ ∑ i : Fin d, ∫ x, H i x ∂π := Finset.sum_le_sum fun i _ => hcoordinate i
    _ = ∫ x, ‖gradient f (WithLp.toLp 2 x)‖ ^ 2 ∂π := by
      rw [← integral_finsetSum _ (fun i _ => hHi i)]
      congr 1
      funext x
      exact (EuclideanSpace.real_norm_sq_eq _).symm
    _ = ∫ x, ‖gradient f x‖ ^ 2 ∂stdGaussian (Space d) := by
      rw [← map_pi_eq_stdGaussian, integral_map htoLp.aemeasurable]
      exact ((gradient_measurable f).norm.pow_const 2).aestronglyMeasurable

#print axioms bounded_gaussian_poincare
end NLA.IE22.LipschitzPoincare
