module

public import NLA.MD06.RadiusEmbedding.EmbeddingNeighbors
public import NLA.MD06.CleanCycleGraph.LiteralStable

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06RadiusEmbedding
open scoped BigOperators
open SimpleGraph
open Reference.MD06CleanCycle
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile Reference.MD06Spectral
attribute [local instance] Classical.propDecidable

theorem actual_clean_radius_nonsynchronized_local_minimum {n : ℕ}
    (G : SimpleGraph (Fin n)) {v : Fin n} (c : G.Walk v v) (hc0 : c.IsCycle)
    (hg : G.Connected) (hcubic : ∀ x, G.degree x = 3)
    (hell : 4 ≤ c.length) (hdiv : 4 ∣ c.length) (R : ℕ) (hR : 4 ≤ R)
    (hc : CleanRadius G c R) (gamma : ℝ) (hgamma : 0 < gamma)
    (hn : 2 ≤ n) (hgap : gamma ≤ LaplacianGap G hn)
    (hlarge : 32*(c.length : ℝ)/((Real.sqrt (1-(Root 4)^2))^4*gamma^2) < (2 : ℝ)^(R-1)) :
    ∃ phi : Configuration n,
      (∀ i, Gradient G (PhaseLift (fun a => phi a)) i = 0) ∧
      IsLocalMin (Energy G) (PhaseLift (fun a => phi a)) ∧
      ¬Synchronized (PhaseLift (fun a => phi a)) ∧
      (∀ i j, G.Adj i j → (1/32 : ℝ) < Real.cos (phi i-phi j)) ∧
      ∀ z : Configuration n, (∑ i, z i) = 0 →
        (Real.sqrt (1-(Root 4)^2)*gamma/2)*‖z‖^2 ≤
          HessianQuadratic G (PhaseLift (fun a => phi a)) (fun i => z i) :=
  actual_clean_embedding_nonsynchronized_local_minimum G hg hell hdiv hR
    (ActualCleanCycleEmbedding c hc0 R hR hell hc hcubic) gamma hgamma hn hgap hlarge

theorem actual_clean_radius_literal_stable_nonsync {n : ℕ}
    (G : SimpleGraph (Fin n)) {v : Fin n} (c : G.Walk v v) (hc0 : c.IsCycle)
    (hg : G.Connected) (hcubic : ∀ x, G.degree x = 3)
    (hell : 4 ≤ c.length) (hdiv : 4 ∣ c.length) (R : ℕ) (hR : 4 ≤ R)
    (hc : CleanRadius G c R) (gamma : ℝ) (hgamma : (1/10 : ℝ) ≤ gamma)
    (hn : 2 ≤ n) (hgap : gamma ≤ LaplacianGap G hn)
    (hlarge : 32*(c.length : ℝ)/((Real.sqrt (1-(Root 4)^2))^4*gamma^2) < (2 : ℝ)^(R-1)) :
    ∃ theta : Phase n, (∀ i, Gradient G theta i = 0) ∧
      IsLocalMin (Energy G) theta ∧ ¬Synchronized theta ∧
      (∀ i j, G.Adj i j → (1/32 : ℝ) < Real.Angle.cos (theta i-theta j)) ∧
      ∀ z : Fin n → ℝ, (∑ i, z i) = 0 →
        (1/320 : ℝ)*(∑ i, (z i)^2) ≤ HessianQuadratic G theta z :=
  actual_clean_embedding_literal_stable_nonsync G hg hell hdiv hR
    (ActualCleanCycleEmbedding c hc0 R hR hell hc hcubic) gamma hgamma hn hgap hlarge

end Reference.MD06RadiusEmbedding
