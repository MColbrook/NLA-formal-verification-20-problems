module

public import NLA.MD06.CleanCycleGraph.EdgeCosines
public import NLA.MD06.CleanCycleGraph.SmallResidual
public import NLA.MD06.CleanCycleGraph.OppositeEdge

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile Reference.MD06Spectral
attribute [local instance] Classical.propDecidable

theorem actual_clean_embedding_nonsynchronized_local_minimum {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hell : 4 ≤ ell) (hdiv : 4 ∣ ell) (hR : 4 ≤ R)
    (e : CleanCycleEmbedding (ell := ell) G hR) (gamma : ℝ) (hgamma : 0 < gamma)
    (hn : 2 ≤ n) (hgap : gamma ≤ LaplacianGap G hn)
    (hlarge : 32*(ell : ℝ)/((Real.sqrt (1-(Root 4)^2))^4*gamma^2) < (2 : ℝ)^(R-1)) :
    ∃ phi : Configuration n,
      (∀ i, Gradient G (PhaseLift (fun a => phi a)) i = 0) ∧
      IsLocalMin (Energy G) (PhaseLift (fun a => phi a)) ∧
      ¬Synchronized (PhaseLift (fun a => phi a)) ∧
      (∀ i j, G.Adj i j → (1/32 : ℝ) < Real.cos (phi i-phi j)) ∧
      ∀ z : Configuration n, (∑ i, z i) = 0 →
        (Real.sqrt (1-(Root 4)^2)*gamma/2)*‖z‖^2 ≤
          HessianQuadratic G (PhaseLift (fun a => phi a)) (fun i => z i) := by
  let initial := EmbeddedProfile e.nodes
  let c : ℝ := Real.sqrt (1-(Root 4)^2)
  have hc : 0 < c := actual_root_cosine_positive (by omega : 4 ≤ 4)
  have hcos := actual_embedded_all_edge_cosines G hR e
  have hsmall := actual_embedded_residual_below_correction_threshold G hell hdiv hR e gamma hgamma hlarge
  let i : Fin n := e.nodes (RootNode (R := R) (⟨1,by omega⟩ : Fin ell))
  let j : Fin n := e.nodes (RootNode (R := R) (⟨2,by omega⟩ : Fin ell))
  have hij : i ≠ j := actual_embedded_opposite_roots_distinct hell e.nodes
  have hforce : (1/2 : ℝ) < |Real.sin (initial i-initial j)| := actual_embedded_opposite_roots_force hell e.nodes hR
  obtain ⟨h,hm,hb,hcrit,hmin,hcos0,hh,hns⟩ := actual_sorted_gap_nonsynchronized_correction
    G hg hn gamma hgamma hgap initial c hc actual_profile_margin_le_one hcos hsmall i j hij hforce
  refine ⟨initial+h,?_,?_,?_,?_,?_⟩
  · simpa only [PiLp.add_apply] using hcrit
  · simpa only [PiLp.add_apply] using hmin
  · simpa only [PiLp.add_apply] using hns
  · intro a b hadj
    have hc0 : (1/32 : ℝ) < c/2 := by
      have hm0 := actual_uniform_cosine_gt_sixteenth
      dsimp [c]
      linarith
    have hh0 := hcos0 a b hadj
    simpa only [PiLp.add_apply] using hc0.trans_le hh0
  · simpa only [PiLp.add_apply] using hh
end Reference.MD06CleanCycle
