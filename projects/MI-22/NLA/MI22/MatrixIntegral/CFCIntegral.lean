module

public import NLA.RA09.LiteralIntegral.Proof
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Real
open NLA.RA09.LiteralIntegral

namespace NLA.MI22.MatrixIntegral

section CStar
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem spectrum_nonnegative (a : A) (ha : 0 ≤ a) {z : ℝ}
    (hz : z ∈ spectrum ℝ a) : 0 ≤ z :=
  (StarOrderedRing.nonneg_iff_spectrum_nonneg a ha.isSelfAdjoint).mp ha z hz

theorem cfc_kernel_integral (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (a : A) (ha : 0 ≤ a) :
    IntegrableOn (fun t => cfc (Real.rpowIntegrand₀₁ p t) a) (Ioi 0) ∧
    CFC.rpow a p = normalization p •
      ∫ t in Ioi 0, cfc (Real.rpowIntegrand₀₁ p t) a := by
  let b := sSup (quasispectrum ℝ a)
  have hb : 0 ≤ b :=
    le_csSup_of_le (b := 0) (IsCompact.bddAbove (by grind)) (by simp) le_rfl
  have hs : spectrum ℝ a ⊆ Ici 0 := fun z hz => spectrum_nonnegative a ha hz
  have hzb : ∀ z ∈ spectrum ℝ a, z ≤ b := by
    intro z hz
    exact le_csSup (IsCompact.bddAbove (quasispectrum.isCompact _))
      (spectrum_subset_quasispectrum ℝ a hz)
  let f := Real.rpowIntegrand₀₁ p
  let bound : ℝ → ℝ := fun t => f t b
  have hc : ContinuousOn (Function.uncurry f) (Ioi 0 ×ˢ spectrum ℝ a) :=
    Real.continuousOn_rpowIntegrand₀₁_uncurry ⟨hp,hp1⟩ _ hs
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ z ∈ spectrum ℝ a,
      ‖f t z‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    rw [Real.norm_of_nonneg (Real.rpowIntegrand₀₁_nonneg hp ht.le (hs hz))]
    exact Real.rpowIntegrand₀₁_monotoneOn ⟨hp,hp1⟩ ht.le (hs hz) hb (hzb z hz)
  have hfinite : HasFiniteIntegral bound (volume.restrict (Ioi 0)) :=
    (Real.integrableOn_rpowIntegrand₀₁_Ioi ⟨hp,hp1⟩ hb).hasFiniteIntegral
  have hi := integrableOn_cfc measurableSet_Ioi f bound a hc hbound hfinite ha.isSelfAdjoint
  refine ⟨hi, ?_⟩
  have he := cfc_setIntegral measurableSet_Ioi f bound a hc hbound hfinite ha.isSelfAdjoint
  have hcontinuous : ContinuousOn (fun x : ℝ => ∫ t in Ioi 0, f t x) (spectrum ℝ a) := by
    have h : ContinuousOn (fun x : ℝ => x^p / normalization p) (spectrum ℝ a) :=
      (Real.continuous_rpow_const hp.le).continuousOn.div_const _
    apply h.congr
    intro x hx
    dsimp only [f]
    rw [Real.integral_rpowIntegrand₀₁_eq_rpow_mul_const ⟨hp,hp1⟩ (hs hx),
      library_constant p hp hp1, normalization]
    simp [div_eq_mul_inv]
  rw [← he, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real ha]
  rw [← cfc_const_mul (normalization p) (fun x : ℝ => ∫ t in Ioi 0, f t x) a hcontinuous]
  apply cfc_congr
  intro x hx
  dsimp only [f]
  rw [Real.rpow_eq_const_mul_integral ⟨hp,hp1⟩ (hs hx), library_constant p hp hp1,
    inv_div, normalization]

#print axioms cfc_kernel_integral

end CStar
end NLA.MI22.MatrixIntegral
