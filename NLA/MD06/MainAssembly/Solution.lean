module

public import NLA.MD06.MainAssembly.RadiusChoice
public import NLA.MD06.MainAssembly.EventBinding
public import NLA.MD06.MainAssembly.CycleTail
public import NLA.MD06.MainAssembly.Probability

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MainAssembly.Interface
open Reference.MD06MainAssembly Reference.MD06Actual Reference.MD06Spectral Reference.MD06RadiusEmbedding
open Reference.MD06FiniteProbability Reference.MD06GraphCycleWalk Reference.MD06CleanRadiusProbability
open Reference.MD06CycleProfile
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_paper_radius_at_least_four (ell : ℕ) : 4≤PaperRadius ell := Reference.MD06MainAssembly.actual_paper_radius_at_least_four ell

theorem actual_paper_radius_inequality (ell : ℕ) (hell : 0<ell) :
    32*(ell : ℝ)/((Real.sqrt (1-(Root 4)^2))^4*(1/10 : ℝ)^2)<
      (2 : ℝ)^(PaperRadius ell-1) := Reference.MD06MainAssembly.actual_paper_radius_inequality ell hell

theorem actual_literal_stable_event_from_gap_clean_cycle {n : ℕ}
    (G : SimpleGraph (Fin n)) (hcubic : G.IsRegularOfDegree 3)
    (ell : ℕ) (hell : 4≤ell) (hdiv : 4∣ell)
    (hgap : (1/10 : ℝ)≤TotalLaplacianGap G)
    (hclean : ¬BadCycleRadius G ell (PaperRadius ell))
    (hcycle : WalkCycleExists G ell) : StableNonsynchronized G := Reference.MD06MainAssembly.actual_literal_stable_event_from_gap_clean_cycle G hcubic ell hell hdiv hgap hclean hcycle

theorem actual_literal_stable_event_not_all_minima_synchronized {n : ℕ}
    (G : SimpleGraph (Fin n)) (h : StableNonsynchronized G) :
    ¬EveryLocalMinimumSynchronized G := Reference.MD06MainAssembly.actual_literal_stable_event_not_all_minima_synchronized G h

theorem actual_literal_stable_failure_union_bound (k ell : ℕ) (hell : 4≤ell) (hdiv : 4∣ell) :
    GraphProbability k (fun G=>¬StableNonsynchronized G)≤
      GraphProbability k (fun G=>¬((1/10 : ℝ)≤TotalLaplacianGap G))+
      GraphProbability k (fun G=>BadCycleRadius G ell (PaperRadius ell))+
      GraphProbability k (fun G=>¬WalkCycleExists G ell) := Reference.MD06MainAssembly.actual_literal_stable_failure_union_bound k ell hell hdiv

theorem actual_fourfold_cycle_mean_lower (q : ℕ) :
    (q : ℝ)+1≤(2 : ℝ)^(4*(q+1))/(2*(4*(q+1) : ℕ)) := Reference.MD06MainAssembly.actual_fourfold_cycle_mean_lower q

theorem actual_fourfold_no_cycle_target_tendsto_zero :
    Tendsto (fun q : ℕ=>Real.exp (-((2 : ℝ)^(4*(q+1))/(2*(4*(q+1) : ℕ)))))
      atTop (𝓝 0) := Reference.MD06MainAssembly.actual_fourfold_no_cycle_target_tendsto_zero 

theorem actual_uniform_total_gap_failure_tendsto_zero :
    Tendsto (fun k=>GraphProbability k (fun G=>¬((1/10 : ℝ)≤TotalLaplacianGap G))) atTop (𝓝 0) := Reference.MD06MainAssembly.actual_uniform_total_gap_failure_tendsto_zero 

theorem actual_uniform_literal_stable_failure_tendsto_zero :
    Tendsto (fun k=>GraphProbability k (fun G=>¬StableNonsynchronized G)) atTop (𝓝 0) := Reference.MD06MainAssembly.actual_uniform_literal_stable_failure_tendsto_zero 

theorem actual_uniform_literal_stable_probability_tendsto_one :
    Tendsto (fun k=>GraphProbability k StableNonsynchronized) atTop (𝓝 1) := Reference.MD06MainAssembly.actual_uniform_literal_stable_probability_tendsto_one 

theorem actual_uniform_all_local_minima_synchronized_tendsto_zero :
    Tendsto (fun k=>GraphProbability k EveryLocalMinimumSynchronized) atTop (𝓝 0) := Reference.MD06MainAssembly.actual_uniform_all_local_minima_synchronized_tendsto_zero 

theorem actual_uniform_cubic_literal_stable_mass_tendsto_one :
    Tendsto (fun k=>((UniformCubic k).toOuterMeasure {G : CubicSample k|StableNonsynchronized G.val}).toReal)
      atTop (𝓝 1) := Reference.MD06MainAssembly.actual_uniform_cubic_literal_stable_mass_tendsto_one 

theorem actual_uniform_cubic_all_local_minima_synchronized_mass_tendsto_zero :
    Tendsto (fun k=>((UniformCubic k).toOuterMeasure {G : CubicSample k|EveryLocalMinimumSynchronized G.val}).toReal)
      atTop (𝓝 0) := Reference.MD06MainAssembly.actual_uniform_cubic_all_local_minima_synchronized_mass_tendsto_zero 

theorem actual_paper_md_main :
    (Tendsto (fun k=>((UniformCubic k).toOuterMeasure {G : CubicSample k|
      ∀ theta : Phase (Size k),IsLocalMin (Energy G.val) theta → Synchronized theta}).toReal)
      atTop (𝓝 0)) ∧
    Tendsto (fun k=>((UniformCubic k).toOuterMeasure {G : CubicSample k|
      ∃ theta : Phase (Size k), (∀ i,Gradient G.val theta i=0) ∧
        IsLocalMin (Energy G.val) theta ∧ ¬Synchronized theta ∧
        (∀ i j,G.val.Adj i j → (1/32 : ℝ)<Real.Angle.cos (theta i-theta j)) ∧
        ∀ z : Fin (Size k)→ℝ,(∑ i,z i)=0 →
          (1/320 : ℝ)*(∑ i,(z i)^2)≤HessianQuadratic G.val theta z}).toReal)
      atTop (𝓝 1) := Reference.MD06MainAssembly.actual_paper_md_main 

#print axioms actual_paper_radius_at_least_four
#print axioms actual_paper_radius_inequality
#print axioms actual_literal_stable_event_from_gap_clean_cycle
#print axioms actual_literal_stable_event_not_all_minima_synchronized
#print axioms actual_literal_stable_failure_union_bound
#print axioms actual_fourfold_cycle_mean_lower
#print axioms actual_fourfold_no_cycle_target_tendsto_zero
#print axioms actual_uniform_total_gap_failure_tendsto_zero
#print axioms actual_uniform_literal_stable_failure_tendsto_zero
#print axioms actual_uniform_literal_stable_probability_tendsto_one
#print axioms actual_uniform_all_local_minima_synchronized_tendsto_zero
#print axioms actual_uniform_cubic_literal_stable_mass_tendsto_one
#print axioms actual_uniform_cubic_all_local_minima_synchronized_mass_tendsto_zero
#print axioms actual_paper_md_main
end Reference.MD06MainAssembly.Interface
