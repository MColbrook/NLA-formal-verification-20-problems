module

public import NLA.MD06.CleanCycleGraph.ResidualNorm

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile
attribute [local instance] Classical.propDecidable

theorem actual_embedded_residual_below_correction_threshold {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hell : 4 ≤ ell) (hdiv : 4 ∣ ell) (hR : 4 ≤ R)
    (e : CleanCycleEmbedding (ell := ell) G hR) (gamma : ℝ) (hgamma : 0 < gamma)
    (hlarge : 32*(ell : ℝ)/((Real.sqrt (1-(Root 4)^2))^4*gamma^2) < (2 : ℝ)^(R-1)) :
    ‖GradientVector G (EmbeddedProfile e.nodes)‖ <
      (Real.sqrt (1-(Root 4)^2))^2*gamma/(4*Real.sqrt 2) := by
  let c : ℝ := Real.sqrt (1-(Root 4)^2)
  have hc : 0 < c := actual_root_cosine_positive (by omega : 4 ≤ 4)
  have hden : 0 < c^4*gamma^2 := by positivity
  have hp : 0 < (2 : ℝ)^(R-1) := by positivity
  have hell0 : 0 < (ell : ℝ) := by exact_mod_cast (show 0 < ell by omega)
  have hspread : 32*(ell : ℝ) < (2 : ℝ)^(R-1)*(c^4*gamma^2) :=
    (div_lt_iff₀ hden).mp hlarge
  have hn := actual_embedded_gradient_norm_square G hell hdiv hR e
  have hmain : ‖GradientVector G (EmbeddedProfile e.nodes)‖^2*(2 : ℝ)^(R-1) =
      (ell : ℝ)*(Root R)^2 := (eq_div_iff (ne_of_gt hp)).mp hn
  have ht := actual_root_interval hR
  have hscaled : ‖GradientVector G (EmbeddedProfile e.nodes)‖^2*(2 : ℝ)^(R-1) < (ell : ℝ) := by
    rw [hmain]
    have hsq : (Root R)^2 < 1 := by nlinarith [ht.1,ht.2]
    nlinarith
  have hbound : 32*‖GradientVector G (EmbeddedProfile e.nodes)‖^2 < c^4*gamma^2 := by
    exact lt_of_mul_lt_mul_left (show (2 : ℝ)^(R-1)*(32*‖GradientVector G (EmbeddedProfile e.nodes)‖^2) <
      (2 : ℝ)^(R-1)*(c^4*gamma^2) by nlinarith [hscaled,hspread]) hp.le
  have hsqrt : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hrho : (c^2*gamma/(4*Real.sqrt 2))^2 = c^4*gamma^2/32 := by
    rw [div_pow,mul_pow,mul_pow,hsqrt]
    ring
  have hrhopos : 0 < c^2*gamma/(4*Real.sqrt 2) := by positivity
  have hnorm := norm_nonneg (GradientVector G (EmbeddedProfile e.nodes))
  change ‖GradientVector G (EmbeddedProfile e.nodes)‖ < c^2*gamma/(4*Real.sqrt 2)
  nlinarith [hrho]
end Reference.MD06CleanCycle
