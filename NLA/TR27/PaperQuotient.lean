module

public import NLA.TR27.PaperProjection
public import NLA.TR27.PaperTensorSupport

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization Classical
namespace NLA.TR27.Paper

theorem chosenParameters_injective (r : ℕ) : Function.Injective (chosenParameters r) := by
  intro i j h
  have hn : ((i : ℕ) + 1 : ℕ) = (j : ℕ) + 1 := by
    exact_mod_cast Option.some.inj h
  exact Fin.ext (by omega)

theorem projectionCenter_ne_zero {D r : ℕ} (hD : 1 ≤ D) (hr : r < D)
    (a : Fin r → Option ℂ) : projectionCenter D r a ≠ 0 := by
  intro hz
  have h := center_not_short_span (k := 0) hD (by omega) a Fin.elim0
  apply h
  rw [hz]
  exact Submodule.zero_mem _

theorem quotientProjection_kernel (D r : ℕ) (a : Fin r → Option ℂ) :
    LinearMap.ker (quotientProjection D r a) = Submodule.span ℂ {projectionCenter D r a} := by
  exact Submodule.ker_mkQ _

theorem quotientProjection_surjective (D r : ℕ) (a : Fin r → Option ℂ) :
    Function.Surjective (quotientProjection D r a) := Submodule.mkQ_surjective _

theorem quotient_dimension {D r : ℕ} (hD : 1 ≤ D) (hr : r < D)
    (a : Fin r → Option ℂ) : Module.finrank ℂ (QuotientSpace D r a) = D := by
  have h := (centerLine D r a).finrank_quotient_add_finrank
  have hc : Module.finrank ℂ (centerLine D r a) = 1 :=
    finrank_span_singleton (projectionCenter_ne_zero hD hr a)
  rw [hc] at h
  simp only [CurveSpace, Module.finrank_pi, Fintype.card_fin] at h
  change Module.finrank ℂ (QuotientSpace D r a) + 1 = D+1 at h
  omega

theorem quotient_curve_independent {D r k : ℕ} (hD : 1 ≤ D) (hk : k+r < D)
    (a : Fin r → Option ℂ) (t : Fin k → Option ℂ) (ht : Function.Injective t) :
    LinearIndependent ℂ (fun i => quotientCurve D r a (t i)) :=
  projected_curve_vectors_independent hD hk a (quotientProjection D r a)
    (quotientProjection_kernel D r a) t ht

theorem quotient_curve_nonzero {D r : ℕ} (hD : 1 ≤ D) (hr : 1+r < D)
    (a : Fin r → Option ℂ) (t : Option ℂ) : quotientCurve D r a t ≠ 0 := by
  have hli := quotient_curve_independent hD hr a (fun _ : Fin 1 => t)
    (Function.injective_of_subsingleton _)
  exact hli.ne_zero 0

theorem quotient_tangent_sum (D r : ℕ) (a : Fin r → Option ℂ) :
    quotientTangent D r a = ∑ i, quotientCurve D r a (a i) := by
  have hz : quotientProjection D r a (projectionCenter D r a) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero (centerLine D r a)).mpr
    exact Submodule.subset_span (Set.mem_singleton _)
  rw [projectionCenter, map_sub, map_sum, sub_eq_zero] at hz
  exact hz

theorem quotient_tangent_nonzero {D r : ℕ} (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : r+r < D) (a : Fin r → Option ℂ) (ha : Function.Injective a) :
    quotientTangent D r a ≠ 0 := by
  intro hz
  have hli := quotient_curve_independent hD hgap a a ha
  have hsum : ∑ i : Fin r, (1 : ℂ) • quotientCurve D r a (a i) = 0 := by
    simpa only [one_smul, ← quotient_tangent_sum] using hz
  have hcoeff := (Fintype.linearIndependent_iff.mp hli) (fun _ => (1 : ℂ)) hsum
  exact one_ne_zero (hcoeff ⟨0, by omega⟩)

theorem quotient_curve_finset_independent {D r : ℕ} (hD : 1 ≤ D)
    (a : Fin r → Option ℂ) (s : Finset (Option ℂ)) (hs : s.card+r < D) :
    LinearIndependent ℂ (fun t : s => quotientCurve D r a t) := by
  classical
  let e := Fintype.equivFin s
  have hli := quotient_curve_independent hD (by simpa only [Fintype.card_coe] using hs)
    a (fun i => (e.symm i : Option ℂ)) (Subtype.val_injective.comp e.symm.injective)
  simpa only [Function.comp_def, Equiv.symm_apply_apply] using hli.comp e e.injective

#print axioms quotient_dimension
#print axioms quotient_tangent_nonzero
end NLA.TR27.Paper
