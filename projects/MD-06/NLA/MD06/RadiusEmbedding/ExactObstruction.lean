module

public import NLA.MD06.RadiusEmbedding.MainBinding

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06RadiusEmbedding
open scoped BigOperators
open SimpleGraph
open Reference.MD06CleanCycle
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile Reference.MD06Spectral
attribute [local instance] Classical.propDecidable

theorem actual_clean_radius_exact_obstruction {n : ℕ}
    (G : SimpleGraph (Fin n)) {v : Fin n} (cycle : G.Walk v v) (hcycle : cycle.IsCycle)
    (hg : G.Connected) (hcubic : ∀ x, G.degree x = 3)
    (hell : 4 ≤ cycle.length) (hdiv : 4 ∣ cycle.length) (R : ℕ) (hR : 4 ≤ R)
    (hclean : CleanRadius G cycle R) (gamma : ℝ) (hgamma : 0 < gamma)
    (hn : 2 ≤ n) (hgap : gamma ≤ LaplacianGap G hn)
    (hlarge : 32*(cycle.length : ℝ)/((Real.sqrt (1-(Root 4)^2))^4*gamma^2) < (2 : ℝ)^(R-1)) :
    ∃ theta : Phase n, (∀ i, Gradient G theta i = 0) ∧
      IsLocalMin (Energy G) theta ∧ ¬Synchronized theta ∧
      (∀ i j, G.Adj i j → Real.sqrt (1-(Root 4)^2)/2 ≤ Real.Angle.cos (theta i-theta j)) ∧
      ∀ z : Fin n → ℝ, (∑ i, z i) = 0 →
        (Real.sqrt (1-(Root 4)^2)*gamma/2)*(∑ i, (z i)^2) ≤ HessianQuadratic G theta z := by
  let e := ActualCleanCycleEmbedding cycle hcycle R hR hell hclean hcubic
  let initial := EmbeddedProfile e.nodes
  let c : ℝ := Real.sqrt (1-(Root 4)^2)
  have hc : 0 < c := actual_root_cosine_positive (by omega : 4 ≤ 4)
  have hcos := actual_embedded_all_edge_cosines G hR e
  have hsmall := actual_embedded_residual_below_correction_threshold G hell hdiv hR e gamma hgamma hlarge
  let i : Fin n := e.nodes (RootNode (R := R) (⟨1,by omega⟩ : Fin cycle.length))
  let j : Fin n := e.nodes (RootNode (R := R) (⟨2,by omega⟩ : Fin cycle.length))
  have hij : i ≠ j := actual_embedded_opposite_roots_distinct hell e.nodes
  have hforce : (1/2 : ℝ) < |Real.sin (initial i-initial j)| :=
    actual_embedded_opposite_roots_force hell e.nodes hR
  obtain ⟨h,hm,hb,hcrit,hmin,hcos0,hh,hns⟩ := actual_sorted_gap_nonsynchronized_correction
    G hg hn gamma hgamma hgap initial c hc actual_profile_margin_le_one hcos hsmall i j hij hforce
  refine ⟨PhaseLift (fun a => (initial+h) a),?_,?_,?_,?_,?_⟩
  · simpa only [PiLp.add_apply] using hcrit
  · simpa only [PiLp.add_apply] using hmin
  · simpa only [PiLp.add_apply] using hns
  · intro a b hadj
    change c/2 ≤ Real.Angle.cos (((initial+h) a : Real.Angle)-((initial+h) b : Real.Angle))
    rw [← Real.Angle.coe_sub,Real.Angle.cos_coe]
    simpa only [PiLp.add_apply] using hcos0 a b hadj
  · intro z hz
    let z' : Configuration n := WithLp.toLp 2 z
    have hz' : (∑ a, z' a) = 0 := by change (∑ a, z a) = 0; exact hz
    have hnorm : ‖z'‖^2 = ∑ a, (z a)^2 := by rw [EuclideanSpace.real_norm_sq_eq]
    have hessian := hh z' hz'
    rw [hnorm] at hessian
    simpa only [PiLp.add_apply] using hessian

end Reference.MD06RadiusEmbedding
