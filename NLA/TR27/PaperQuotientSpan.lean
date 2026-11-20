module

public import NLA.TR27.PaperQuotient
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization Classical
namespace NLA.TR27.Paper

theorem curve_vectors_span (D : ℕ) :
    Submodule.span ℂ (Set.range (curveVector D)) = ⊤ := by
  have hinj : Function.Injective (fun i : Fin (D+1) => (i.val : ℂ)) := by
    intro i j hij
    apply Fin.ext
    dsimp only at hij
    exact_mod_cast hij
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro v ⟨i, rfl⟩
  exact ⟨some (i.val : ℂ), rfl⟩

theorem quotient_curve_span (D r : ℕ) (a : Fin r → Option ℂ) :
    Submodule.span ℂ (Set.range (quotientCurve D r a)) = ⊤ := by
  have h := congrArg (Submodule.map (quotientProjection D r a)) (curve_vectors_span D)
  rw [Submodule.map_span, Submodule.map_top,
    LinearMap.range_eq_top.mpr (quotientProjection_surjective D r a)] at h
  rw [← Set.range_comp] at h
  exact h

theorem quotient_projective_span {D r : ℕ} (hD : 1 ≤ D) (hr : 1+r < D)
    (a : Fin r → Option ℂ) :
    Submodule.span ℂ (Projectivization.rep '' quotientPoints D r a) = ⊤ := by
  apply top_unique
  rw [← quotient_curve_span D r a]
  apply Submodule.span_le.mpr
  rintro v ⟨t, rfl⟩
  apply (projective_span_mk (quotientPoints D r a) _ (quotient_curve_nonzero hD hr a t)).mp
  apply Projectivization.Subspace.subset_span
  exact ⟨t, represents_mk _ _⟩

#print axioms quotient_projective_span
end NLA.TR27.Paper
