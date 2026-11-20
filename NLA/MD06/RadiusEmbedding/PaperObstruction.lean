module

public import NLA.MD06.RadiusEmbedding.ExactObstruction
public import NLA.MD06.RadiusEmbedding.PaperSpectrumDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06RadiusEmbedding
open scoped BigOperators
open SimpleGraph
open Reference.MD06Actual Reference.MD06CycleProfile Reference.MD06Spectral
attribute [local instance] Classical.propDecidable

theorem actual_cubic_dimension {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n)
    (hcubic : ∀ x, G.degree x = 3) : 4 ≤ n := by
  have hd := G.degree_lt_card_verts v
  rw [hcubic v,Fintype.card_fin] at hd
  omega

theorem actual_paper_md_obstruction {n : ℕ}
    (G : SimpleGraph (Fin n)) {v : Fin n} (cycle : G.Walk v v) (hcycle : cycle.IsCycle)
    (hg : G.Connected) (hcubic : ∀ x, G.degree x = 3)
    (hpositive : 0 < cycle.length) (hdiv : 4 ∣ cycle.length) (R : ℕ) (hR : 4 ≤ R)
    (hclean : CleanRadius G cycle R) (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : gamma ≤ TotalLaplacianGap G)
    (hlarge : 32*(cycle.length : ℝ)/((Real.sqrt (1-(Root 4)^2))^4*gamma^2) < (2 : ℝ)^(R-1)) :
    ∃ theta : Phase n, (∀ i, Gradient G theta i = 0) ∧
      IsLocalMin (Energy G) theta ∧ ¬Synchronized theta ∧
      (∀ i j, G.Adj i j → Real.sqrt (1-(Root 4)^2)/2 ≤ Real.Angle.cos (theta i-theta j)) ∧
      ∀ z : Fin n → ℝ, (∑ i, z i) = 0 →
        (Real.sqrt (1-(Root 4)^2)*gamma/2)*(∑ i, (z i)^2) ≤ HessianQuadratic G theta z := by
  have hell : 4 ≤ cycle.length := by
    obtain ⟨k,hk⟩ := hdiv
    omega
  have hn : 2 ≤ n := by have h := actual_cubic_dimension G v hcubic; omega
  have hgap' : gamma ≤ LaplacianGap G hn := by
    simpa only [TotalLaplacianGap,dif_pos hn] using hgap
  exact actual_clean_radius_exact_obstruction G cycle hcycle hg hcubic hell hdiv R hR
    hclean gamma hgamma hn hgap' hlarge

end Reference.MD06RadiusEmbedding
