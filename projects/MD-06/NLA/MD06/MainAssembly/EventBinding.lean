module

public import NLA.MD06.MainAssembly.EventDefinitions
public import NLA.MD06.GraphCycleWalk.Definitions
public import NLA.MD06.MainAssembly.RadiusChoice
public import NLA.MD06.GapConnected.GapConnected
public import NLA.MD06.RadiusEmbedding.MainBinding
public import NLA.MD06.CleanRadiusProbability.Bounds
public import NLA.MD06.FiniteProbability.FiniteBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MainAssembly
open Reference.MD06Actual Reference.MD06Spectral Reference.MD06RadiusEmbedding
open Reference.MD06FiniteProbability Reference.MD06GraphCycleWalk Reference.MD06CleanRadiusProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_literal_stable_event_from_gap_clean_cycle {n : ℕ}
    (G : SimpleGraph (Fin n)) (hcubic : G.IsRegularOfDegree 3)
    (ell : ℕ) (hell : 4≤ell) (hdiv : 4∣ell)
    (hgap : (1/10 : ℝ)≤TotalLaplacianGap G)
    (hclean : ¬BadCycleRadius G ell (PaperRadius ell))
    (hcycle : WalkCycleExists G ell) : StableNonsynchronized G := by
  obtain ⟨v,c,hc,hclen⟩:=hcycle
  have hg : G.Connected := Reference.MD06GapConnected.actual_positive_total_gap_connected G (by linarith)
  have hn : 2≤n := by
    have hd:=G.degree_lt_card_verts v
    rw [hcubic.degree_eq v,Fintype.card_fin] at hd
    omega
  have hgap' : (1/10 : ℝ)≤LaplacianGap G hn := by
    simpa only [TotalLaplacianGap,dif_pos hn] using hgap
  have hclean' : CleanRadius G c (PaperRadius ell) :=
    (actual_no_bad_cycle_radius_iff G ell (PaperRadius ell)).mp hclean v c hc hclen
  have hb:=actual_clean_radius_literal_stable_nonsync G c hc hg (fun x=>hcubic.degree_eq x)
    (by omega) (by rwa [hclen]) (PaperRadius ell) (actual_paper_radius_at_least_four ell)
    hclean' (1/10) le_rfl hn hgap'
    (by rw [hclen];exact actual_paper_radius_inequality ell (by omega))
  exact hb

theorem actual_literal_stable_event_not_all_minima_synchronized {n : ℕ}
    (G : SimpleGraph (Fin n)) (h : StableNonsynchronized G) :
    ¬EveryLocalMinimumSynchronized G := by
  obtain ⟨theta,hcrit,hmin,hns,hcos,hh⟩:=h
  exact fun hall=>hns (hall theta hmin)

theorem actual_literal_stable_failure_union_bound (k ell : ℕ) (hell : 4≤ell) (hdiv : 4∣ell) :
    GraphProbability k (fun G=>¬StableNonsynchronized G)≤
      GraphProbability k (fun G=>¬((1/10 : ℝ)≤TotalLaplacianGap G))+
      GraphProbability k (fun G=>BadCycleRadius G ell (PaperRadius ell))+
      GraphProbability k (fun G=>¬WalkCycleExists G ell) := by
  have hb:=actual_graph_failure_probability_bound k StableNonsynchronized
    (fun G=>(1/10 : ℝ)≤TotalLaplacianGap G)
    (fun G=>¬BadCycleRadius G ell (PaperRadius ell))
    (fun G=>WalkCycleExists G ell)
    (fun G hG hgap hclean hcycle=>actual_literal_stable_event_from_gap_clean_cycle G hG ell hell hdiv hgap hclean hcycle)
  simpa only [not_not] using hb

#print axioms actual_literal_stable_event_from_gap_clean_cycle
#print axioms actual_literal_stable_event_not_all_minima_synchronized
#print axioms actual_literal_stable_failure_union_bound
end Reference.MD06MainAssembly
