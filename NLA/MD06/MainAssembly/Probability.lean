module

public import NLA.MD06.MainAssembly.EventBinding
public import NLA.MD06.MainAssembly.CycleTail
public import NLA.MD06.SpectralProbability.Probability
public import NLA.MD06.GraphCycleWalk.Proofs

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MainAssembly
open Reference.MD06Actual Reference.MD06Spectral Reference.MD06RadiusEmbedding
open Reference.MD06FiniteProbability Reference.MD06GraphCycleWalk Reference.MD06CleanRadiusProbability
open Filter Topology
attribute [local instance] Classical.propDecidable

theorem actual_uniform_total_gap_failure_tendsto_zero :
    Tendsto (fun k=>GraphProbability k (fun G=>¬((1/10 : ℝ)≤TotalLaplacianGap G))) atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ=>(1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have he:=hconst.sub Reference.RootMD06SpectralProbability.actual_uniform_graph_sorted_gap_probability_tendsto_one
  have hid (k : ℕ) : GraphProbability k (fun G=>¬((1/10 : ℝ)≤TotalLaplacianGap G))=
      1-GraphProbability k (fun G=>(1/10 : ℝ)≤LaplacianGap G (by dsimp [Size];omega)) := by
    rw [←actual_graph_probability_complement]
    apply congrArg (GraphProbability k)
    funext G
    simp only [TotalLaplacianGap,dif_pos (by dsimp [Size];omega : 2≤Size k)]
  simpa only [hid,sub_self] using he

theorem actual_uniform_literal_stable_failure_tendsto_zero :
    Tendsto (fun k=>GraphProbability k (fun G=>¬StableNonsynchronized G)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun k=>ha.trans_le (by rw [actual_graph_probability_sample_formula];exact actual_counting_probability_nonnegative _))
  · intro eps heps
    obtain ⟨q,hq⟩:=(actual_fourfold_no_cycle_target_tendsto_zero.eventually (gt_mem_nhds (show (0 : ℝ)<eps/2 by linarith))).exists
    let ell:=4*(q+1)
    have hell : 4≤ell := by dsimp [ell];omega
    have hdiv : 4∣ell := ⟨q+1,rfl⟩
    have hcycle:=actual_uniform_no_walk_cycle_limit ell (by omega)
    have hclean:=actual_bad_cycle_radius_probability_limit ell (PaperRadius ell)
    have hsum:= (actual_uniform_total_gap_failure_tendsto_zero.add hclean).add hcycle
    simp only [zero_add] at hsum
    have htarget : Real.exp (-((2 : ℝ)^ell/(2*ell)))<eps := by
      have hsmall : Real.exp (-((2 : ℝ)^ell/(2*ell)))<eps/2 := by exact hq
      linarith
    filter_upwards [hsum.eventually (gt_mem_nhds htarget)] with k hk
    exact (actual_literal_stable_failure_union_bound k ell hell hdiv).trans_lt hk

theorem actual_uniform_literal_stable_probability_tendsto_one :
    Tendsto (fun k=>GraphProbability k StableNonsynchronized) atTop (𝓝 1) := by
  have hconst : Tendsto (fun _ : ℕ=>(1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have h:=hconst.sub actual_uniform_literal_stable_failure_tendsto_zero
  have he (k : ℕ) : GraphProbability k StableNonsynchronized=
      1-GraphProbability k (fun G=>¬StableNonsynchronized G) := by
    rw [actual_graph_probability_complement]
    ring
  simpa only [he,sub_zero] using h

theorem actual_uniform_all_local_minima_synchronized_tendsto_zero :
    Tendsto (fun k=>GraphProbability k EveryLocalMinimumSynchronized) atTop (𝓝 0) := by
  apply squeeze_zero ?_ ?_ actual_uniform_literal_stable_failure_tendsto_zero
  · intro k
    rw [actual_graph_probability_sample_formula]
    exact actual_counting_probability_nonnegative _
  · intro k
    apply actual_regular_graph_probability_monotone
    intro G hG hall hs
    exact actual_literal_stable_event_not_all_minima_synchronized G hs hall

theorem actual_uniform_cubic_literal_stable_mass_tendsto_one :
    Tendsto (fun k=>((UniformCubic k).toOuterMeasure {G : CubicSample k|StableNonsynchronized G.val}).toReal)
      atTop (𝓝 1) := by
  simpa only [actual_graph_probability_uniform_real] using actual_uniform_literal_stable_probability_tendsto_one

theorem actual_uniform_cubic_all_local_minima_synchronized_mass_tendsto_zero :
    Tendsto (fun k=>((UniformCubic k).toOuterMeasure {G : CubicSample k|EveryLocalMinimumSynchronized G.val}).toReal)
      atTop (𝓝 0) := by
  simpa only [actual_graph_probability_uniform_real] using actual_uniform_all_local_minima_synchronized_tendsto_zero

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
      atTop (𝓝 1) :=
  ⟨actual_uniform_cubic_all_local_minima_synchronized_mass_tendsto_zero,
    actual_uniform_cubic_literal_stable_mass_tendsto_one⟩

#print axioms actual_uniform_total_gap_failure_tendsto_zero
#print axioms actual_uniform_literal_stable_failure_tendsto_zero
#print axioms actual_uniform_literal_stable_probability_tendsto_one
#print axioms actual_uniform_all_local_minima_synchronized_tendsto_zero
#print axioms actual_uniform_cubic_literal_stable_mass_tendsto_one
#print axioms actual_uniform_cubic_all_local_minima_synchronized_mass_tendsto_zero

#print axioms actual_paper_md_main
end Reference.MD06MainAssembly
