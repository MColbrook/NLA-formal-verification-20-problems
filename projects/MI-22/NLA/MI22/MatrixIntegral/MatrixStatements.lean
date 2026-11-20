module

public import NLA.MI22.MatrixIntegral.NormBound
public import NLA.MI22.MatrixIntegral.ResolventOrder
public import NLA.MI22.Definitions
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NLA.RA09.LiteralIntegral
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace NLA.MI22.MatrixIntegral

theorem matrix_resolvent {n : ℕ} (P : Mat n) (t : ℝ) :
    resolvent t P = (t • (1 : Mat n) + P)⁻¹ := by
  simp only [resolvent, Matrix.nonsing_inv_eq_ringInverse, Algebra.algebraMap_eq_smul_one]

theorem actual_matrix_power_integrable {n : ℕ} (P : Mat n) (hP : P.PosSemidef)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IntegrableOn (fun t : ℝ => t^(p-1) • (P * (P+t • (1 : Mat n))⁻¹)) (Ioi 0) := by
  have h := power_kernel_integrable p hp hp1 P hP.nonneg
  simpa only [powerKernel, matrix_resolvent, add_comm P] using h

theorem actual_matrix_power_integral {n : ℕ} (P : Mat n) (hP : P.PosSemidef)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    spectralPower P p = (Real.sin (Real.pi*p) / Real.pi) •
      ∫ t : ℝ in Ioi 0, t^(p-1) • (P * (P+t • (1 : Mat n))⁻¹) := by
  have h := power_integral_representation p hp hp1 P hP.nonneg
  simpa only [spectralPower, normalization, powerKernel, matrix_resolvent, add_comm P] using h

theorem actual_matrix_cfc_power_integral {n : ℕ} (P : Mat n) (hP : P.PosSemidef)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    cfc (fun x : ℝ => x^p) P = (Real.sin (Real.pi*p) / Real.pi) •
      ∫ t : ℝ in Ioi 0, t^(p-1) • (P * (P+t • (1 : Mat n))⁻¹) := by
  have h := actual_matrix_power_integral P hP p hp hp1
  rw [spectralPower, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hP.nonneg] at h
  exact h

theorem actual_matrix_multiplicative_resolvent_identity {n : ℕ} (P : Mat n)
    (hP : P.PosSemidef) (t : ℝ) (ht : 0 < t) :
    P * (P+t • (1 : Mat n))⁻¹ = 1-t • (P+t • (1 : Mat n))⁻¹ := by
  simpa only [matrix_resolvent, add_comm P] using
    multiplicative_resolvent_identity t ht P hP.nonneg

theorem actual_matrix_multiplicative_resolvent_monotone {n : ℕ} (P Q : Mat n)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hPQ : P ≤ Q) (t : ℝ) (ht : 0 < t) :
    P * (P+t • (1 : Mat n))⁻¹ ≤ Q * (Q+t • (1 : Mat n))⁻¹ := by
  simpa only [matrix_resolvent, add_comm P, add_comm Q] using
    multiplicative_resolvent_monotone t ht P Q hP.nonneg hQ.nonneg hPQ

theorem actual_matrix_resolvent_difference {n : ℕ} (P Q : Mat n)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (t : ℝ) (ht : 0 < t) :
    (t • (1 : Mat n)+Q)⁻¹ - (t • (1 : Mat n)+P)⁻¹ =
      (t • (1 : Mat n)+Q)⁻¹ * (P-Q) * (t • (1 : Mat n)+P)⁻¹ := by
  simpa only [matrix_resolvent] using resolvent_difference t ht P Q hP.nonneg hQ.nonneg

theorem actual_matrix_difference_integrable {n : ℕ} (P Q : Mat n)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IntegrableOn (fun t : ℝ => t^p •
      ((t • (1 : Mat n)+Q)⁻¹ * (P-Q) * (t • (1 : Mat n)+P)⁻¹)) (Ioi 0) := by
  simpa only [differenceKernel, matrix_resolvent] using
    difference_kernel_integrable p hp hp1 P Q hP.nonneg hQ.nonneg

theorem actual_matrix_difference_integral {n : ℕ} (P Q : Mat n)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    spectralPower P p - spectralPower Q p = (Real.sin (Real.pi*p) / Real.pi) •
      ∫ t : ℝ in Ioi 0, t^p •
        ((t • (1 : Mat n)+Q)⁻¹ * (P-Q) * (t • (1 : Mat n)+P)⁻¹) := by
  simpa only [spectralPower, normalization, differenceKernel, matrix_resolvent] using
    difference_integral_representation p hp hp1 P Q hP.nonneg hQ.nonneg

theorem actual_matrix_difference_norm_integrable {n : ℕ} (P Q : Mat n)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    IntegrableOn (fun t : ℝ => operatorNorm (t^p •
      ((t • (1 : Mat n)+Q)⁻¹ * (P-Q) * (t • (1 : Mat n)+P)⁻¹))) (Ioi 0) := by
  unfold IntegrableOn
  simpa only [operatorNorm, Matrix.cstar_norm_def] using
    (actual_matrix_difference_integrable P Q hP hQ p hp hp1).norm

theorem actual_matrix_integrand_norm_bound {n : ℕ} (P Q : Mat n)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (p t m : ℝ) (ht : 0 < t) (hm : 0 < m)
    (hmP : m • (1 : Mat n) ≤ P) (hmQ : m • (1 : Mat n) ≤ Q) :
    operatorNorm (t^p • ((t • (1 : Mat n)+Q)⁻¹ * (P-Q) * (t • (1 : Mat n)+P)⁻¹)) ≤
      (t^p / (t+m)^2) * operatorNorm (P-Q) := by
  have h := difference_kernel_norm_bound p t m ht hm P Q hP.nonneg hQ.nonneg
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hmP)
    (by simpa only [Algebra.algebraMap_eq_smul_one] using hmQ)
  simpa only [operatorNorm, Matrix.cstar_norm_def, differenceKernel, matrix_resolvent,
    LiteralDerivative.derivativeIntegrand] using h

#print axioms actual_matrix_power_integral
#print axioms actual_matrix_difference_integral
#print axioms actual_matrix_integrand_norm_bound

end NLA.MI22.MatrixIntegral
