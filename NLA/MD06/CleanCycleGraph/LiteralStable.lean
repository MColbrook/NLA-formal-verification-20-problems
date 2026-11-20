module

public import NLA.MD06.CleanCycleGraph.Obstruction

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile Reference.MD06Spectral
attribute [local instance] Classical.propDecidable

theorem actual_clean_embedding_literal_stable_nonsync {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hell : 4 ≤ ell) (hdiv : 4 ∣ ell) (hR : 4 ≤ R)
    (e : CleanCycleEmbedding (ell := ell) G hR) (gamma : ℝ) (hgamma : (1/10 : ℝ) ≤ gamma)
    (hn : 2 ≤ n) (hgap : gamma ≤ LaplacianGap G hn)
    (hlarge : 32*(ell : ℝ)/((Real.sqrt (1-(Root 4)^2))^4*gamma^2) < (2 : ℝ)^(R-1)) :
    ∃ theta : Phase n, (∀ i, Gradient G theta i = 0) ∧
      IsLocalMin (Energy G) theta ∧ ¬Synchronized theta ∧
      (∀ i j, G.Adj i j → (1/32 : ℝ) < Real.Angle.cos (theta i-theta j)) ∧
      ∀ z : Fin n → ℝ, (∑ i, z i) = 0 →
        (1/320 : ℝ)*(∑ i, (z i)^2) ≤ HessianQuadratic G theta z := by
  have hg0 : 0 < gamma := by linarith
  obtain ⟨phi,hcrit,hmin,hns,hcos,hh⟩ := actual_clean_embedding_nonsynchronized_local_minimum
    G hg hell hdiv hR e gamma hg0 hn hgap hlarge
  refine ⟨PhaseLift (fun a => phi a),hcrit,hmin,hns,?_,?_⟩
  · intro i j hij
    change (1/32 : ℝ) < Real.Angle.cos ((phi i : Real.Angle)-(phi j : Real.Angle))
    rw [←Real.Angle.coe_sub,Real.Angle.cos_coe]
    exact hcos i j hij
  · intro z hz
    let z' : Configuration n := WithLp.toLp 2 z
    have hz' : (∑ i, z' i) = 0 := by change (∑ i, z i) = 0; exact hz
    have hnorm : ‖z'‖^2 = ∑ i, (z i)^2 := by rw [EuclideanSpace.real_norm_sq_eq]
    have hmargin : (1/320 : ℝ) ≤ Real.sqrt (1-(Root 4)^2)*gamma/2 := by
      have hc := actual_uniform_cosine_gt_sixteenth
      have hp := mul_nonneg (sub_nonneg.mpr hc.le) (sub_nonneg.mpr hgamma)
      nlinarith
    have hl := mul_le_mul_of_nonneg_right hmargin (sq_nonneg ‖z'‖)
    have hh' := hh z' hz'
    have hr := hl.trans hh'
    rw [hnorm] at hr
    exact hr
end Reference.MD06CleanCycle
