module

public import NLA.TR27.ArbitrarySmoothImage
public import NLA.TR27.ArbitraryRecoveryHomogeneous
public import NLA.TR27.ArbitraryBorder
public import NLA.TR27.ArbitraryBirational

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] coordinateProjectiveTopology

theorem paper_parameter_closed_geometry (D r : ℕ) (hr : 3 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) :
    ∃ E : QuotientSpace D r (fun i => some (a i)) ≃ₗ[ℂ] (Fin D → ℂ),
      ∃ I : Ideal (ImageCoordinatePolynomial D),
        (∀ w, E (quotientProjection D r (fun i => some (a i)) w) = parameterProjection D r a w) ∧
        let X := ProjectiveVariety.mk D E I
        X.Admissible ∧ X.points = quotientPoints D r (fun i => some (a i)) ∧
          X.IsClosed X.points ∧ X.IsIrreducible X.points := by
  let E := parameterCoordinateEquiv D r (by omega) a
  let X := parameterImageVariety D r (by omega) a
  have hX := parameter_image_admissible D r (by omega) (by omega) (by omega) a
  exact ⟨E,parameterImageIdeal D r a,parameterCoordinateEquiv_projection D r (by omega) a,
    hX,parameter_image_points D r (by omega) (by omega) (by omega) a,
    admissible_points_closed X hX,admissible_points_irreducible X hX⟩

theorem paper_parameter_smooth_geometry (D r : ℕ) (hr : 3 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) :
    ∃ F : (ℙ ℂ (Fin 2 → ℂ)) → ℙ ℂ (Fin D → ℂ),
      (∀ t : Option ℂ, Represents (parameterCoordinateCurve D r a t) (F (projectiveLinePoint t))) ∧
      Topology.IsClosedEmbedding F ∧
      (∀ p ∈ Set.range F, HasProjectiveAnalyticGraph (Set.range F) p) := by
  exact ⟨parameterProjectiveMap D r (by omega) (by omega) (by omega) a,
    parameterProjectiveMap_parameter_rep D r (by omega) (by omega) (by omega) a,
    parameterProjectiveMap_closedEmbedding D r (by omega) (by omega) (by omega) a,
    parameter_all_points_analytic_graph D r (by omega) hD a ha ha0⟩

theorem paper_parameter_rational_recovery (D r : ℕ) (hr : 3 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) :
    (parameterRecoveryException D r hD a ≠ 0) ∧
      Set.Finite {t : ℂ | (parameterRecoveryException D r hD a).eval t = 0} ∧
      (∃ d : ℕ, (parameterRecoveryNumerator D r hD (by omega) a).IsHomogeneous d ∧
        (parameterRecoveryDenominator D r hD a).IsHomogeneous d) ∧
      (∀ (t : ℂ) (p : ℙ ℂ (Fin D → ℂ)),
        Represents (parameterCoordinateCurve D r a (some t)) p →
        (parameterRecoveryException D r hD a).eval t ≠ 0 →
        MvPolynomial.eval p.rep (parameterRecoveryDenominator D r hD a) ≠ 0 ∧
          MvPolynomial.eval p.rep (parameterRecoveryNumerator D r hD (by omega) a)/
            MvPolynomial.eval p.rep (parameterRecoveryDenominator D r hD a) = t) := by
  have he := parameter_recovery_exception_finite D r hD a
  exact ⟨he.1,he.2,parameter_recovery_homogeneous D r (by omega) hD a,
    parameter_projective_rational_recovery D r (by omega) hD a ha ha0⟩

theorem paper_parameter_border_two (D r : ℕ) (hr : 3 ≤ r) (hgap : 3*r ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) :
    ∃ E : QuotientSpace D r (fun i => some (a i)) ≃ₗ[ℂ] (Fin D → ℂ),
      ∃ I : Ideal (ImageCoordinatePolynomial D),
        (∀ w, E (quotientProjection D r (fun i => some (a i)) w) = parameterProjection D r a w) ∧
        let X := ProjectiveVariety.mk D E I
        X.points = quotientPoints D r (fun i => some (a i)) ∧
          ∃ hv : quotientTangent D r (fun i => some (a i)) ≠ 0,
            borderRank X (Projectivization.mk ℂ _ hv) = 2 := by
  exact ⟨parameterCoordinateEquiv D r (by omega) a,parameterImageIdeal D r a,
    parameterCoordinateEquiv_projection D r (by omega) a,
    parameter_image_points D r (by omega) (by omega) (by omega) a,
    parameter_tangent_border_two D r hr hgap a ha⟩

theorem paper_parameter_birational_geometry (D r : ℕ) (hr : 3 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) :
    (parameterBirationalException D r (by omega) hD a ≠ 0) ∧
      Set.Finite {t : ℂ | (parameterBirationalException D r (by omega) hD a).eval t = 0} ∧
      (parameterBirationalOpen D r (by omega) hD a).Nonempty ∧
      ∃ E : QuotientSpace D r (fun i => some (a i)) ≃ₗ[ℂ] (Fin D → ℂ),
        ∃ I : Ideal (ImageCoordinatePolynomial D),
          (∀ w, E (quotientProjection D r (fun i => some (a i)) w) = parameterProjection D r a w) ∧
          let X := ProjectiveVariety.mk D E I
          X.Admissible ∧ X.points = quotientPoints D r (fun i => some (a i)) ∧
          X.zariskiClosure (parameterBirationalOpen D r (by omega) hD a) = X.points ∧
          (∃ e : {t : ℂ // (parameterBirationalException D r (by omega) hD a).eval t ≠ 0} ≃
              {p // p ∈ parameterBirationalOpen D r (by omega) hD a},
            (∀ t, Represents (quotientCurve D r (fun i => some (a i)) (some t.val)) (e t).val) ∧
            (∀ p, (e.symm p).val = parameterBirationalRecovery D r (by omega) hD a (E p.val.rep))) := by
  let E := parameterCoordinateEquiv D r (by omega) a
  let X := parameterImageVariety D r (by omega) a
  have hX := parameter_image_admissible D r (by omega) (by omega) (by omega) a
  have hpts : X.points = quotientPoints D r (fun i => some (a i)) :=
    parameter_image_points D r (by omega) (by omega) (by omega) a
  have hexc := parameter_birational_exception_nonzero D r (by omega) hD a
  refine ⟨hexc,Polynomial.finite_setOfPred_isRoot hexc,
    parameter_birational_nonempty D r (by omega) hD a ha ha0,
    E,parameterImageIdeal D r a,parameterCoordinateEquiv_projection D r (by omega) a,
    hX,hpts, ?_,parameter_birational_equiv D r (by omega) hD a ha ha0⟩
  rw [hpts]
  exact parameter_birational_dense D r (by omega) hD a ha ha0

#print axioms paper_parameter_birational_geometry

#print axioms paper_parameter_closed_geometry
#print axioms paper_parameter_smooth_geometry
#print axioms paper_parameter_rational_recovery
#print axioms paper_parameter_border_two
end NLA.TR27.Paper
