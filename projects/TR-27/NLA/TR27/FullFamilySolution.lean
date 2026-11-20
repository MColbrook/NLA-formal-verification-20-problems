module

public import NLA.TR27.PaperFamilyComplete

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

theorem paper_image_smooth_graphs (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (hgap : 2*(r+1) ≤ D) :
    Set.range (projectiveCurveMap D r hD hr) = coordinateImagePoints D r hD ∧
    (∀ p ∈ coordinateImagePoints D r hD, HasProjectiveAnalyticGraph (coordinateImagePoints D r hD) p) := by
  exact ⟨projectiveCurveMap_range_eq_coordinateImagePoints D r hD hr,
    coordinateImagePoints_analytic_graph D r hD hr hgap⟩

theorem paper_full_family (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
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
  exact full_paper_family r m hr hm

#print axioms paper_image_smooth_graphs
#print axioms paper_full_family

end NLA.TR27.Paper
