module

public import NLA.TR27.PaperProjectiveCurveMap

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

def projectiveLinePoint : Option ℂ → ℙ ℂ (Fin 2 → ℂ)
  | none => Projectivization.mk ℂ (![0,1]) (by simp)
  | some t => Projectivization.mk ℂ (![1,t]) (by simp)

theorem projectiveLinePoint_surjective : Function.Surjective projectiveLinePoint := by
  intro p
  by_cases h0 : p.rep 0 = 0
  · have h1 : p.rep 1 ≠ 0 := by
      intro hz
      apply p.rep_nonzero
      ext i
      fin_cases i <;> simp [h0,hz]
    refine ⟨none, ?_⟩
    apply Eq.symm
    apply (represents_iff_eq_mk (![0,1]) (by simp) p).mp
    refine ⟨p.rep 1,h1, ?_⟩
    ext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, h0]
  · refine ⟨some (p.rep 1 / p.rep 0), ?_⟩
    apply Eq.symm
    apply (represents_iff_eq_mk (![1,p.rep 1 / p.rep 0]) (by simp) p).mp
    refine ⟨p.rep 0,h0, ?_⟩
    ext i
    fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, h0]
    field_simp

theorem projectiveCurveMap_parameter_rep (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (t : Option ℂ) : Represents (coordinateCurve D r hD t)
      (projectiveCurveMap D r hD hr (projectiveLinePoint t)) := by
  cases t with
  | none =>
    have hv : imageHomogeneousMap D r hD (![0,1]) ≠ 0 :=
      fun h => (by simp : (![0,1] : Fin 2 → ℂ) ≠ 0)
        ((imageHomogeneousMap_eq_zero_iff D r hD hr _).mp h)
    have h := represents_mk (imageHomogeneousMap D r hD (![0,1])) hv
    simpa only [projectiveLinePoint, projectiveCurveMap_mk, imageHomogeneousMap_infinity] using h
  | some t =>
    have hv : imageHomogeneousMap D r hD (![1,t]) ≠ 0 :=
      fun h => (by simp : (![1,t] : Fin 2 → ℂ) ≠ 0)
        ((imageHomogeneousMap_eq_zero_iff D r hD hr _).mp h)
    have h := represents_mk (imageHomogeneousMap D r hD (![1,t])) hv
    simpa only [projectiveLinePoint, projectiveCurveMap_mk, imageHomogeneousMap_finite] using h

theorem coordinate_curve_parameter_unique (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (hgap : r+2 < D) (s t : Option ℂ) (p : ℙ ℂ (Fin D → ℂ))
    (hs : Represents (coordinateCurve D r hD s) p)
    (ht : Represents (coordinateCurve D r hD t) p) : s = t := by
  by_contra hst
  have hinj : Function.Injective (![s,t] : Fin 2 → Option ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hli := quotient_curve_independent (by omega : 1 ≤ D) (by omega : 2+r < D)
    (chosenParameters r) (![s,t]) hinj
  obtain ⟨a,ha,hea⟩ := hs
  obtain ⟨b,hb,heb⟩ := ht
  have he : a • quotientCurve D r (chosenParameters r) s -
      b • quotientCurve D r (chosenParameters r) t = 0 := by
    apply (quotientCoordinateEquiv D r hD hr).injective
    simp only [map_sub, map_smul, map_zero, quotientCurve, quotientCoordinateEquiv_projection]
    change a • coordinateCurve D r hD s - b • coordinateCurve D r hD t = 0
    rw [← hea, ← heb, sub_self]
  have hz : ∑ i : Fin 2, (![a,-b] : Fin 2 → ℂ) i •
      quotientCurve D r (chosenParameters r) ((![s,t] : Fin 2 → Option ℂ) i) = 0 := by
    simpa [Fin.sum_univ_two, sub_eq_add_neg] using he
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) (![a,-b]) hz
  exact ha (hcoeff 0)

theorem projectiveCurveMap_injective (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (hgap : r+2 < D) : Function.Injective (projectiveCurveMap D r hD hr) := by
  intro p q hpq
  obtain ⟨s,rfl⟩ := projectiveLinePoint_surjective p
  obtain ⟨t,rfl⟩ := projectiveLinePoint_surjective q
  have hs := projectiveCurveMap_parameter_rep D r hD hr s
  rw [hpq] at hs
  have hst := coordinate_curve_parameter_unique D r hD hr hgap s t _ hs
    (projectiveCurveMap_parameter_rep D r hD hr t)
  rw [hst]

/-- An embedding for the usual source and target quotient topologies,
obtained from compactness and the actual secant-independence theorem. -/
theorem projectiveCurveMap_closedEmbedding (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (hgap : r+2 < D) : Topology.IsClosedEmbedding (projectiveCurveMap D r hD hr) := by
  letI := coordinateProjective_compact 2
  letI := coordinateProjective_t2 D
  exact (continuous_projectiveCurveMap D r hD hr).isClosedEmbedding
    (projectiveCurveMap_injective D r hD hr hgap)

theorem projectiveCurveMap_range (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    Set.range (projectiveCurveMap D r hD hr) =
      {p | ∃ t : Option ℂ, Represents (coordinateCurve D r hD t) p} := by
  ext p
  constructor
  · rintro ⟨q,rfl⟩
    obtain ⟨t,rfl⟩ := projectiveLinePoint_surjective q
    exact ⟨t,projectiveCurveMap_parameter_rep D r hD hr t⟩
  · rintro ⟨t,ht⟩
    have h := projectiveCurveMap_parameter_rep D r hD hr t
    have hv := represents_nonzero _ _ h
    refine ⟨projectiveLinePoint t, ?_⟩
    exact ((represents_iff_eq_mk _ hv _).mp h).trans ((represents_iff_eq_mk _ hv _).mp ht).symm

#print axioms projectiveCurveMap_closedEmbedding
#print axioms projectiveCurveMap_range
end NLA.TR27.Paper
