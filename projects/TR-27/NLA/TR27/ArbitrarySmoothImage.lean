module

public import NLA.TR27.ArbitraryParametersSolution
public import NLA.TR27.ArbitraryClosedImage
public import NLA.TR27.PaperImageSmooth

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Topology LinearAlgebra.Projectivization
open Filter
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

def parameterProjectiveMap (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) (p : ℙ ℂ (Fin 2 → ℂ)) : ℙ ℂ (Fin D → ℂ) :=
  Projectivization.mk ℂ (parameterHomogeneousMap D r a p.rep)
    (fun h => p.rep_nonzero ((parameterHomogeneousMap_eq_zero_iff D r hD hr hgap a p.rep).mp h))

theorem parameterProjectiveMap_mk (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    parameterProjectiveMap D r hD hr hgap a (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (parameterHomogeneousMap D r a v)
        (fun h => hv ((parameterHomogeneousMap_eq_zero_iff D r hD hr hgap a v).mp h)) := by
  obtain ⟨c,hc,heq⟩ := represents_mk v hv
  unfold parameterProjectiveMap
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨c^D,by rw [heq,parameterHomogeneousMap_smul]⟩

theorem parameterProjectiveMap_parameter_rep (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) (t : Option ℂ) :
    Represents (parameterCoordinateCurve D r a t)
      (parameterProjectiveMap D r hD hr hgap a (projectiveLinePoint t)) := by
  cases t with
  | none =>
    rw [projectiveLinePoint,parameterProjectiveMap_mk]
    simpa only [parameterHomogeneousMap_infinity D r hD a] using
      represents_mk (parameterHomogeneousMap D r a (![0,1]))
        (fun h => (by simp : (![0,1] : Fin 2 → ℂ) ≠ 0)
          ((parameterHomogeneousMap_eq_zero_iff D r hD hr hgap a _).mp h))
  | some t =>
    rw [projectiveLinePoint,parameterProjectiveMap_mk]
    simpa only [parameterHomogeneousMap_finite] using
      represents_mk (parameterHomogeneousMap D r a (![1,t]))
        (fun h => (by simp : (![1,t] : Fin 2 → ℂ) ≠ 0)
          ((parameterHomogeneousMap_eq_zero_iff D r hD hr hgap a _).mp h))

theorem continuous_parameterProjectiveMap (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) :
    Continuous (parameterProjectiveMap D r hD hr hgap a) := by
  have hc : Continuous (parameterHomogeneousMap D r a) := by
    apply continuous_pi
    intro j
    simp only [parameterHomogeneousMap_apply]
    fun_prop
  apply continuous_coinduced_dom.mpr
  let F : {v : Fin 2 → ℂ // v ≠ 0} → {v : Fin D → ℂ // v ≠ 0} :=
    fun v => ⟨parameterHomogeneousMap D r a v.val,
      fun h => v.property ((parameterHomogeneousMap_eq_zero_iff D r hD hr hgap a v.val).mp h)⟩
  have hF : Continuous F := (hc.comp continuous_subtype_val).subtype_mk _
  have h := (continuous_coordinate_projective_mk D).comp hF
  convert h using 1
  funext v
  exact parameterProjectiveMap_mk D r hD hr hgap a v.val v.property

theorem parameterProjectiveMap_injective (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : r+2 < D) (a : Fin r → ℂ) :
    Function.Injective (parameterProjectiveMap D r hD hr (by omega) a) := by
  have unique (s t : Option ℂ) (p : ℙ ℂ (Fin D → ℂ))
      (hs : Represents (parameterCoordinateCurve D r a s) p)
      (ht : Represents (parameterCoordinateCurve D r a t) p) : s = t := by
    by_contra hst
    have hinj : Function.Injective (![s,t] : Fin 2 → Option ℂ) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hli := quotient_curve_independent hD (by omega : 2+r < D)
      (fun i => some (a i)) (![s,t]) hinj
    obtain ⟨b,hb,heb⟩ := hs
    obtain ⟨c,hc,hec⟩ := ht
    have he : b • quotientCurve D r (fun i => some (a i)) s -
        c • quotientCurve D r (fun i => some (a i)) t = 0 := by
      apply (parameterCoordinateEquiv D r hr a).injective
      simp only [map_sub,map_smul,map_zero,quotientCurve,parameterCoordinateEquiv_projection]
      change b • parameterCoordinateCurve D r a s-c • parameterCoordinateCurve D r a t = 0
      rw [← heb,← hec,sub_self]
    have hz : ∑ i : Fin 2, (![b,-c] : Fin 2 → ℂ) i •
        quotientCurve D r (fun i => some (a i)) ((![s,t] : Fin 2 → Option ℂ) i) = 0 := by
      simpa [Fin.sum_univ_two,sub_eq_add_neg] using he
    exact hb ((Fintype.linearIndependent_iff.mp hli) (![b,-c]) hz 0)
  intro p q hpq
  obtain ⟨s,rfl⟩ := projectiveLinePoint_surjective p
  obtain ⟨t,rfl⟩ := projectiveLinePoint_surjective q
  have hs := parameterProjectiveMap_parameter_rep D r hD hr (by omega) a s
  rw [hpq] at hs
  rw [unique s t _ hs (parameterProjectiveMap_parameter_rep D r hD hr (by omega) a t)]

theorem parameterProjectiveMap_closedEmbedding (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : r+2 < D) (a : Fin r → ℂ) :
    Topology.IsClosedEmbedding (parameterProjectiveMap D r hD hr (by omega) a) := by
  letI := coordinateProjective_compact 2
  letI := coordinateProjective_t2 D
  exact (continuous_parameterProjectiveMap D r hD hr (by omega) a).isClosedEmbedding
    (parameterProjectiveMap_injective D r hD hr hgap a)

theorem parameter_projected_tangent_independent (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) (t : Option ℂ) (α β : ℂ)
    (h : α • parameterCoordinateCurve D r a t +
      β • parameterProjection D r a (curveTangent D t) = 0) : α = 0 ∧ β = 0 := by
  apply projected_curve_tangent_coefficients_eq_zero hr hD a ha ha0 t α β
  apply (parameterCoordinateEquiv D r hr a).injective
  simp only [map_add,map_smul,map_zero,quotientCurve,parameterCoordinateEquiv_projection]
  exact h

theorem parameter_finite_local_chart (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) (t : ℂ) :
    HasProjectiveAnalyticGraph (Set.range (parameterProjectiveMap D r (by omega) hr (by omega) a))
      (parameterProjectiveMap D r (by omega) hr (by omega) a (projectiveLinePoint (some t))) := by
  let P : CurveSpace D →L[ℂ] (Fin D → ℂ) := (parameterProjection D r a).toContinuousLinearMap
  have hd := P.hasFDerivAt.comp_hasDerivAt t (curveVector_hasDerivAt D t)
  obtain ⟨i,j,hi,d,hd0,hf⟩ := normalized_chart_has_nonzero_derivative
    (fun t => parameterCoordinateCurve D r a (some t))
    (parameterProjection D r a (curveTangent D (some t))) t hd
    (parameter_projected_tangent_independent D r hr hD a ha ha0 (some t))
  have han (k : Fin D) : AnalyticAt ℂ
      (fun t => parameterCoordinateCurve D r a (some t) k) t := by
    change AnalyticAt ℂ (fun t => (r : ℂ)*t^k.succ.val+
      projectionCenter D r (fun i => some (a i)) k.succ*(t^0)) t
    fun_prop
  obtain ⟨g,hgval,hg,hleft,hright,hgraph⟩ := normalized_chart_analytic_inverse _ t han i j hi d hd0 hf
  have hrep (z : ℂ) : Represents (parameterCoordinateCurve D r a (some z))
      (parameterProjectiveMap D r (by omega) hr (by omega) a ((projectiveLineChart 0).symm z)) := by
    rw [projectiveLineChart_zero_inverse]
    exact parameterProjectiveMap_parameter_rep D r (by omega) hr (by omega) a (some z)
  have h := projective_graph_of_local_inverse (parameterProjectiveMap D r (by omega) hr (by omega) a)
    (parameterProjectiveMap_closedEmbedding D r (by omega) hr (by omega) a).isEmbedding
    (projectiveLineChart 0).symm (projectiveLineChart_inverse_isOpenEmbedding 0)
    (fun t => parameterCoordinateCurve D r a (some t)) hrep t i j hi g hgval hg hleft hright hgraph
  simpa only [projectiveLineChart_zero_inverse] using h

theorem parameter_infinity_local_chart (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) :
    HasProjectiveAnalyticGraph (Set.range (parameterProjectiveMap D r (by omega) hr (by omega) a))
      (parameterProjectiveMap D r (by omega) hr (by omega) a (projectiveLinePoint none)) := by
  let P : CurveSpace D →L[ℂ] (Fin D → ℂ) := (parameterProjection D r a).toContinuousLinearMap
  let f := fun t => parameterProjection D r a (infinityChart D t)
  have hd := P.hasFDerivAt.comp_hasDerivAt 0 (infinityChart_hasDerivAt D)
  have hi0 : ∀ α β : ℂ, α • f 0+β • parameterProjection D r a (curveTangent D none) = 0 →
      α = 0 ∧ β = 0 := by
    simp only [f,infinityChart_zero]
    exact parameter_projected_tangent_independent D r hr hD a ha ha0 none
  obtain ⟨i,j,hi,d,hd0,hf⟩ := normalized_chart_has_nonzero_derivative f _ 0 hd hi0
  have han (k : Fin D) : AnalyticAt ℂ (fun t => f t k) 0 := by
    change AnalyticAt ℂ (fun t => (r : ℂ)*t^(D-k.succ.val)+
      projectionCenter D r (fun i => some (a i)) k.succ*(t^D)) 0
    fun_prop
  obtain ⟨g,hgval,hg,hleft,hright,hgraph⟩ := normalized_chart_analytic_inverse f 0 han i j hi d hd0 hf
  have hrev (z : ℂ) : parameterHomogeneousMap D r a (![z,1]) = f z := by
    ext k
    simp [parameterHomogeneousMap_apply,f,parameterProjection,infinityChart]
  have hrep (z : ℂ) : Represents (f z)
      (parameterProjectiveMap D r (by omega) hr (by omega) a ((projectiveLineChart 1).symm z)) := by
    rw [projectiveLineChart_one_inverse,parameterProjectiveMap_mk]
    simpa only [hrev] using
      represents_mk (parameterHomogeneousMap D r a (![z,1]))
        (fun h => (by simp : (![z,1] : Fin 2 → ℂ) ≠ 0)
          ((parameterHomogeneousMap_eq_zero_iff D r (by omega) hr (by omega) a _).mp h))
  have h := projective_graph_of_local_inverse (parameterProjectiveMap D r (by omega) hr (by omega) a)
    (parameterProjectiveMap_closedEmbedding D r (by omega) hr (by omega) a).isEmbedding
    (projectiveLineChart 1).symm (projectiveLineChart_inverse_isOpenEmbedding 1)
    f hrep 0 i j hi g hgval hg hleft hright hgraph
  simpa only [projectiveLineChart_one_inverse,projectiveLinePoint] using h

theorem parameter_all_points_analytic_graph (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) :
    ∀ p ∈ Set.range (parameterProjectiveMap D r (by omega) hr (by omega) a),
      HasProjectiveAnalyticGraph (Set.range (parameterProjectiveMap D r (by omega) hr (by omega) a)) p := by
  rintro p ⟨q,rfl⟩
  obtain ⟨t,rfl⟩ := projectiveLinePoint_surjective q
  cases t with
  | none => exact parameter_infinity_local_chart D r hr hD a ha ha0
  | some t => exact parameter_finite_local_chart D r hr hD a ha ha0 t

#print axioms parameter_all_points_analytic_graph
#print axioms parameterProjectiveMap_closedEmbedding
end NLA.TR27.Paper
