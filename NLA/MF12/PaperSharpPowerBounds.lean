module

public import NLA.MF12.PaperSharpNorms
public import NLA.MF12.PowerBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator
namespace NLA.MF12.Paper

theorem nat_succ_mul_contraction_power (u : ℝ) (hu : 0 < u) (hu1 : u < 1) (q : ℕ) :
    ((q : ℝ)+1)*u^q ≤ (1-u)⁻¹ := by
  have hδ : 0 < 1-u := by linarith
  have hden : 0 < 1+(q:ℝ)*(1-u) := by positivity
  have hb := (bernoulli_loss (1-u) hδ.le (by linarith) q).1
  have hb' : u^q ≤ 1/(1+(q:ℝ)*(1-u)) := by simpa using hb
  have hp := (le_div_iff₀ hden).mp hb'
  rw [← one_div, le_div_iff₀ hδ]
  nlinarith [mul_nonneg hu.le (pow_nonneg hu.le q)]

theorem jordan_pair_energy (a b H x y : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hH : 0 ≤ H) (hab : a+b ≤ H) :
    (a*x+b*y)^2+(a*y)^2 ≤ H^2*(x^2+y^2) := by
  have hbase : (a*x+b*y)^2+(a*y)^2 ≤ (a+b)^2*(x^2+y^2) := by
    nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x-y)),
      mul_nonneg (mul_nonneg ha hb) (add_nonneg (sq_nonneg x) (sq_nonneg y)),
      sq_nonneg (b*x)]
  exact hbase.trans (mul_le_mul_of_nonneg_right
    ((sq_le_sq₀ (add_nonneg ha hb) hH).mpr hab) (by positivity))

theorem parameter_power_sharp_norm (lam μ : ℝ) (hlam : 0 < lam)
    (hμ : 0 < μ) (hlμ : lam ≤ μ) (hμ1 : μ < 1) (q : ℕ) :
    spectralNorm (parameterMatrix lam μ ^ q) ≤ (1-μ)⁻¹ := by
  let H : ℝ := (1-μ)⁻¹
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hH1 : 1 ≤ H := by
    dsimp [H]
    rw [one_le_inv₀ (by linarith)]
    linarith
  have hlamp := pow_nonneg hlam.le q
  have hμp := pow_nonneg hμ.le q
  have hlamoff := mul_nonneg (Nat.cast_nonneg q) hlamp
  have hμoff := mul_nonneg (Nat.cast_nonneg q) hμp
  have hlamH : lam^q+(q:ℝ)*lam^q ≤ H := by
    have hpow := pow_le_pow_left₀ hlam.le hlμ q
    have hle := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (q:ℝ)+1)
    have hu := nat_succ_mul_contraction_power μ hμ hμ1 q
    dsimp [H]
    nlinarith
  have hμH : μ^q+(q:ℝ)*μ^q ≤ H := by
    have hu := nat_succ_mul_contraction_power μ hμ hμ1 q
    dsimp [H]
    nlinarith
  apply ContinuousLinearMap.opNorm_le_bound _ hH
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hH (norm_nonneg x))).mp
  have h₁ := jordan_pair_energy (lam^q) ((q:ℝ)*lam^q) H (x 1) (x 2)
    hlamp hlamoff hH hlamH
  have h₂ := jordan_pair_energy (μ^q) ((q:ℝ)*μ^q) H (x 3) (x 4)
    hμp hμoff hH hμH
  have hsq : 1 ≤ H^2 := by nlinarith
  have h₀ := mul_le_mul_of_nonneg_right hsq (sq_nonneg (x 0))
  have h₅ := mul_le_mul_of_nonneg_right hsq (sq_nonneg (x 5))
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp [parameter_power, parameterPower, Matrix.toEuclideanCLM_toLp,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at ⊢
  nlinarith

#print axioms parameter_power_sharp_norm
end NLA.MF12.Paper
