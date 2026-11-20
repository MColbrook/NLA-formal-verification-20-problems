module

public import NLA.TR27.PaperSmoothGraphDefinitions
public import NLA.TR27.PaperProjectiveLineCharts
public import NLA.TR27.PaperLocalImageGraph
public import NLA.TR27.PaperLocalAnalyticCharts

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Topology LinearAlgebra.Projectivization
open Filter
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

theorem projective_graph_of_local_inverse
    {A : Type*} [TopologicalSpace A] {n : ℕ}
    (F : A → ℙ ℂ (Fin n → ℂ)) (hF : Topology.IsEmbedding F)
    (P : ℂ → A) (hP : Topology.IsOpenEmbedding P) (f : ℂ → Fin n → ℂ)
    (hrep : ∀ t, Represents (f t) (F (P t))) (a : ℂ)
    (i j : Fin n) (hi : f a i ≠ 0) (g : ℂ → ℂ)
    (hgval : g (f a j / f a i) = a) (hg : AnalyticAt ℂ g (f a j / f a i))
    (hleft : ∀ᶠ t in 𝓝 a, g (f t j / f t i) = t)
    (hright : ∀ᶠ z in 𝓝 (f a j / f a i), f (g z) j / f (g z) i = z)
    (hgraph : ∀ k, AnalyticAt ℂ (fun z => f (g z) k / f (g z) i) (f a j / f a i)) :
    HasProjectiveAnalyticGraph (Set.range F) (F (P a)) := by
  let R := fun (p : ℙ ℂ (Fin n → ℂ)) k => projectiveCoordinateRatio i k p
  have hratio (t : ℂ) (k : Fin n) : R (F (P t)) k = f t k / f t i :=
    projectiveCoordinateRatio_of_represents i k _ _ (hrep t)
  have ha : (F (P a)).rep i ≠ 0 := by
    obtain ⟨c,hc,heq⟩ := hrep a
    rw [heq]
    change c * f a i ≠ 0
    exact mul_ne_zero hc hi
  have hR : ContinuousOn (fun q => R q j) {p | p.rep i ≠ 0} := by
    intro p hp
    exact (continuousAt_projectiveCoordinateRatio i j p hp).continuousWithinAt
  have hv := embedded_local_analytic_graph F hF P hP R j {p | p.rep i ≠ 0}
    (projective_coordinate_domain_open i) hR a ha g
    (by simpa only [hratio] using hgval)
    (by simpa only [hratio] using hg)
    (by simpa only [hratio] using hleft)
    (by simpa only [hratio] using hright)
    (by simpa only [hratio] using hgraph)
  obtain ⟨V,W,hVo,hpaV,hWo,hpaW,heq,hV,hG⟩ := hv
  let H := fun z => F (P (g z))
  have hij : i ≠ j := by
    intro he
    subst j
    have hsub : V ⊆ {1} := by
      intro z hz
      have ht := (hV z hz).2
      change projectiveCoordinateRatio i i (H z) = z at ht
      have hden : (H z).rep i ≠ 0 := (hV z hz).1
      change z = 1
      calc
        z = (H z).rep i / (H z).rep i := ht.symm
        _ = 1 := div_self hden
    have hp1 : R (F (P a)) i = 1 := hsub hpaV
    have h1 : (1 : ℂ) ∈ V := hp1 ▸ hpaV
    have hsingleton : V = {1} := Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr h1)
    exact not_isOpen_singleton (1 : ℂ) (hsingleton ▸ hVo)
  refine ⟨i,j,hij,ha,V,W,H,hVo,hpaV,hWo,hpaW,heq, ?_,hV,hG⟩
  change F (P (g (R (F (P a)) j))) = F (P a)
  rw [hratio, hgval]

theorem finite_image_analytic_graph (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (hgap : 2*(r+1) ≤ D) (a : ℂ) :
    HasProjectiveAnalyticGraph (Set.range (projectiveCurveMap D r hD hr))
      (projectiveCurveMap D r hD hr (projectiveLinePoint (some a))) := by
  obtain ⟨i,j,hi,g,hgval,hg,hleft,hright,hgraph⟩ := finite_projective_analytic_chart D r hD hr hgap a
  have hrep (t : ℂ) : Represents (coordinateCurve D r hD (some t))
      (projectiveCurveMap D r hD hr ((projectiveLineChart 0).symm t)) := by
    rw [projectiveLineChart_zero_inverse]
    exact projectiveCurveMap_parameter_rep D r hD hr (some t)
  have h := projective_graph_of_local_inverse (projectiveCurveMap D r hD hr)
    (projectiveCurveMap_closedEmbedding D r hD hr (by omega)).isEmbedding
    (projectiveLineChart 0).symm (projectiveLineChart_inverse_isOpenEmbedding 0)
    (fun t => coordinateCurve D r hD (some t)) hrep a i j hi g hgval hg hleft hright hgraph
  simpa only [projectiveLineChart_zero_inverse] using h

theorem infinity_image_analytic_graph (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (hgap : 2*(r+1) ≤ D) :
    HasProjectiveAnalyticGraph (Set.range (projectiveCurveMap D r hD hr))
      (projectiveCurveMap D r hD hr (projectiveLinePoint none)) := by
  obtain ⟨i,j,hi,g,hgval,hg,hleft,hright,hgraph⟩ := infinity_projective_analytic_chart D r hD hr hgap
  have h := projective_graph_of_local_inverse (projectiveCurveMap D r hD hr)
    (projectiveCurveMap_closedEmbedding D r hD hr (by omega)).isEmbedding
    (projectiveLineChart 1).symm (projectiveLineChart_inverse_isOpenEmbedding 1)
    (fun t => coordinateProjection D r hD (infinityChart D t))
    (projectiveCurveMap_reverse_chart_rep D r hD hr) 0 i j hi g hgval hg hleft hright hgraph
  simpa only [projectiveLineChart_one_inverse, projectiveLinePoint] using h

/-- Every point of the entire image, including infinity, has an actual local
analytic graph in the inherited standard projective charts. -/
theorem image_all_points_analytic_graph (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (hgap : 2*(r+1) ≤ D) :
    ∀ p ∈ Set.range (projectiveCurveMap D r hD hr),
      HasProjectiveAnalyticGraph (Set.range (projectiveCurveMap D r hD hr)) p := by
  rintro p ⟨q,rfl⟩
  obtain ⟨t,rfl⟩ := projectiveLinePoint_surjective q
  cases t with
  | none => exact infinity_image_analytic_graph D r hD hr hgap
  | some a => exact finite_image_analytic_graph D r hD hr hgap a

theorem projectiveCurveMap_range_eq_coordinateImagePoints (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    Set.range (projectiveCurveMap D r hD hr) = coordinateImagePoints D r hD := by
  rw [projectiveCurveMap_range]
  ext p
  change (∃ t, Represents (coordinateCurve D r hD t) p) ↔
    p.rep ∈ MvPolynomial.zeroLocus ℂ (imageIdeal D r hD)
  rw [image_whole_closed_cone D r hD hr]
  constructor
  · rintro ⟨t,c,hc,heq⟩
    exact Or.inr ⟨c,hc,t,heq⟩
  · rintro (hz | ⟨c,hc,t,heq⟩)
    · exact (p.rep_nonzero hz).elim
    · exact ⟨t,c,hc,heq⟩

theorem coordinateImagePoints_analytic_graph (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (hgap : 2*(r+1) ≤ D) :
    ∀ p ∈ coordinateImagePoints D r hD, HasProjectiveAnalyticGraph (coordinateImagePoints D r hD) p := by
  rw [← projectiveCurveMap_range_eq_coordinateImagePoints D r hD hr]
  exact image_all_points_analytic_graph D r hD hr hgap

#print axioms coordinateImagePoints_analytic_graph
#print axioms image_all_points_analytic_graph
end NLA.TR27.Paper
