module

public import NLA.TR27.PaperImageSmooth
public import NLA.TR27.PaperRationalGeometry
public import NLA.TR27.PaperFamilyAlgebraic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

/-- All geometric and rank conclusions on the literal same family and point.
Smoothness is expressed by whole-image analytic graphs in standard affine
projective charts; rationality specifies both maps on a nonempty dense open. -/
theorem full_paper_family (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    ∃ hD : 2 ≤ familyDegree r m, ∃ h5 : 5 ≤ familyDegree r m,
      let D := familyDegree r m
      let E := quotientCoordinateEquiv D r hD hr
      let X := ProjectiveVariety.mk D E (imageIdeal D r hD)
      (∀ w, E (quotientProjection D r (chosenParameters r) w) = coordinateProjection D r hD w) ∧
      X.Admissible ∧ X.IsClosed X.points ∧ X.IsIrreducible X.points ∧
      X.points = quotientPoints D r (chosenParameters r) ∧
      Set.range (projectiveCurveMap D r hD hr) = coordinateImagePoints D r hD ∧
      (∀ p ∈ coordinateImagePoints D r hD, HasProjectiveAnalyticGraph (coordinateImagePoints D r hD) p) ∧
      Topology.IsClosedEmbedding (projectiveCurveMap D r hD hr) ∧
      recoveryPolynomial r ≠ 0 ∧
      Set.Finite {t : ℂ | Polynomial.eval t (recoveryPolynomial r) = 0} ∧
      (recoveryOpenPoints D r h5 hr).Nonempty ∧
      X.IsClosed {p | MvPolynomial.eval (E p.rep) (recoveryDenominator D r h5) = 0} ∧
      X.zariskiClosure (recoveryOpenPoints D r h5 hr) = X.points ∧
      (∃ e : {t : ℂ // Polynomial.eval t (recoveryPolynomial r) ≠ 0} ≃
          {p // p ∈ recoveryOpenPoints D r h5 hr},
        (∀ t, Represents (quotientCurve D r (chosenParameters r) (some t.val)) (e t).val) ∧
        (∀ p, (e.symm p).val = rationalRecovery D r h5 (E p.val.rep))) ∧
      (∃ hv : quotientTangent D r (chosenParameters r) ≠ 0,
        borderRank X (Projectivization.mk ℂ _ hv) = 2 ∧
        projectiveRank X.points (Projectivization.mk ℂ _ hv) = r ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ m →
          projectiveRank (productPoints X.points k) (powerPoint (Projectivization.mk ℂ _ hv) k) = r^k) := by
  have hgap := family_degree_gap hr hm
  have hD : 2 ≤ familyDegree r m := by omega
  have h5 : 5 ≤ familyDegree r m := by omega
  have hgeom : 2*(r+1) ≤ familyDegree r m := by omega
  let D := familyDegree r m
  let E := quotientCoordinateEquiv D r hD hr
  let X := ProjectiveVariety.mk D E (imageIdeal D r hD)
  have hX : X.Admissible := quotient_image_admissible D r hD hr
  have hpoints : X.points = quotientPoints D r (chosenParameters r) := quotient_image_points D r hD hr
  refine ⟨hD,h5,quotientCoordinateEquiv_projection D r hD hr,hX,
    admissible_points_closed X hX,admissible_points_irreducible X hX,hpoints,
    projectiveCurveMap_range_eq_coordinateImagePoints D r hD hr,
    coordinateImagePoints_analytic_graph D r hD hr hgeom,
    projectiveCurveMap_closedEmbedding D r hD hr (by dsimp [D]; omega),
    recoveryPolynomial_ne_zero hr,recovery_exceptional_parameters_finite r hr,
    recovery_open_nonempty D r h5 hr,recovery_zero_set_closed D r h5 hr, ?_,
    recovery_open_equiv D r h5 hr, ?_⟩
  · rw [hpoints]
    exact recovery_open_dense D r h5 hr
  · obtain ⟨hv,hmin,hb⟩ := projected_tangent_border_two D r hD hr hgap
    refine ⟨hv,hb, ?_, ?_⟩
    · rw [hpoints]
      exact (quotient_tangent_rank (by dsimp [D]; omega : 1 ≤ D) (by omega : 1 ≤ r)
        hgap (chosenParameters r) (chosenParameters_injective r)).csInf_eq
    · intro k hk hkm
      rw [hpoints]
      obtain ⟨hv',hpow⟩ := family_tensor_rank hr hm hkm
      exact hpow.csInf_eq

#print axioms full_paper_family
end NLA.TR27.Paper
