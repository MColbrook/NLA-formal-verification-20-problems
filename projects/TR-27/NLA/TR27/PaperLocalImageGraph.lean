module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Topology
open Filter
namespace NLA.TR27.Paper

/-- A local analytic inverse on a parametrized branch, together with a genuine
global embedding, describes the WHOLE image near the point. The distinguished
ambient coordinate is exactly the graph parameter. -/
theorem embedded_local_analytic_graph
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] {n : ℕ}
    (F : A → B) (hF : Topology.IsEmbedding F)
    (P : ℂ → A) (hP : Topology.IsOpenEmbedding P)
    (R : B → Fin n → ℂ) (j : Fin n) (B₀ : Set B) (hB₀ : IsOpen B₀)
    (hR : ContinuousOn (fun q => R q j) B₀) (a : ℂ) (ha : F (P a) ∈ B₀)
    (g : ℂ → ℂ) (hgval : g (R (F (P a)) j) = a)
    (hg : AnalyticAt ℂ g (R (F (P a)) j))
    (hleft : ∀ᶠ t in 𝓝 a, g (R (F (P t)) j) = t)
    (hright : ∀ᶠ z in 𝓝 (R (F (P a)) j), R (F (P (g z))) j = z)
    (hgraph : ∀ k, AnalyticAt ℂ (fun z => R (F (P (g z))) k) (R (F (P a)) j)) :
    ∃ V : Set ℂ, ∃ W : Set B,
      IsOpen V ∧ R (F (P a)) j ∈ V ∧ IsOpen W ∧ F (P a) ∈ W ∧
      Set.range F ∩ W = (fun z => F (P (g z))) '' V ∧
      (∀ z ∈ V, F (P (g z)) ∈ B₀ ∧ R (F (P (g z))) j = z) ∧
      (∀ k, AnalyticOnNhd ℂ (fun z => R (F (P (g z))) k) V) := by
  let f : ℂ → ℂ := fun t => R (F (P t)) j
  have hc : Continuous (fun t => F (P t)) := hF.continuous.comp hP.continuous
  have hdom : ∀ᶠ t in 𝓝 a, F (P t) ∈ B₀ := hc.continuousAt (hB₀.mem_nhds ha)
  obtain ⟨U,hU,hUo,haU⟩ := eventually_nhds_iff.mp (hleft.and hdom)
  have hgc : Tendsto g (𝓝 (f a)) (𝓝 a) := by
    have h := hg.continuousAt
    change Tendsto g (𝓝 (R (F (P a)) j)) (𝓝 (g (R (F (P a)) j))) at h
    rw [hgval] at h
    exact h
  have hgU : ∀ᶠ z in 𝓝 (f a), g z ∈ U := hgc (hUo.mem_nhds haU)
  have hgraphs : ∀ᶠ z in 𝓝 (f a), ∀ k, AnalyticAt ℂ (fun w => R (F (P (g w))) k) z :=
    eventually_all.mpr (fun k => (hgraph k).eventually_analyticAt)
  obtain ⟨V,hV,hVo,hfaV⟩ := eventually_nhds_iff.mp (hgU.and (hright.and hgraphs))
  have hfc : ContinuousOn f U := hR.comp hc.continuousOn (fun t ht => (hU t ht).2)
  let U' := U ∩ f ⁻¹' V
  have hU'o : IsOpen U' := (continuousOn_open_iff hUo).mp hfc V hVo
  have haU' : a ∈ U' := ⟨haU,hfaV⟩
  obtain ⟨W,hWo,hW⟩ := hF.isInducing.image_eq_isOpen_inter_range (hP.isOpenMap U' hU'o)
  have himage : F '' (P '' U') = (fun z => F (P (g z))) '' V := by
    apply Set.Subset.antisymm
    · rintro q ⟨p,⟨t,ht,rfl⟩,rfl⟩
      refine ⟨f t, ht.2, ?_⟩
      change F (P (g (R (F (P t)) j))) = F (P t)
      rw [(hU t ht.1).1]
    · rintro q ⟨z,hz,rfl⟩
      refine ⟨P (g z), ⟨g z, ?_, rfl⟩, rfl⟩
      refine ⟨(hV z hz).1, ?_⟩
      change R (F (P (g z))) j ∈ V
      rw [(hV z hz).2.1]
      exact hz
  have hmem : F (P a) ∈ W := by
    have h : F (P a) ∈ F '' (P '' U') := ⟨P a,⟨a,haU',rfl⟩,rfl⟩
    rw [hW] at h
    exact h.1
  refine ⟨V,W,hVo,hfaV,hWo,hmem, ?_, ?_, ?_⟩
  · rw [Set.inter_comm, ← hW, himage]
  · intro z hz
    exact ⟨(hU (g z) (hV z hz).1).2,(hV z hz).2.1⟩
  · intro k z hz
    exact (hV z hz).2.2 k

#print axioms embedded_local_analytic_graph
end NLA.TR27.Paper
