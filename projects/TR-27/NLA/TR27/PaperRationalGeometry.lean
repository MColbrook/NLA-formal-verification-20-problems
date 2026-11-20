module

public import NLA.TR27.PaperRationalGeometryDefinitions
public import NLA.TR27.PaperRationalInverse
public import NLA.TR27.PaperPrincipalOpen
public import NLA.TR27.PaperImageGeometry

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

theorem recoveryDenominator_homogeneous (D r : ℕ) (hD : 5 ≤ D) :
    (recoveryDenominator D r hD).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_C_mul_X _ _).add
    (MvPolynomial.isHomogeneous_C_mul_X _ _)).add (MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem recoveryNumerator_homogeneous (D r : ℕ) (hD : 5 ≤ D) :
    (recoveryNumerator D r hD).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_C_mul_X _ _).add
    (MvPolynomial.isHomogeneous_C_mul_X _ _)).add (MvPolynomial.isHomogeneous_C_mul_X _ _)

theorem recoveryDenominator_infinity (D r : ℕ) (hD : 5 ≤ D) :
    MvPolynomial.eval (coordinateCurve D r (by omega) none) (recoveryDenominator D r hD) = 0 := by
  have hcoord (j : Fin 4) (hj : j.val ≤ 2) :
      coordinateCurve D r (by omega) none (recoveryIndex D hD j) = 0 := by
    have hn : j.val+2 ≠ D := by omega
    simp [coordinateCurve, coordinateProjection, curveVector, pivotIndex,
      recoveryIndex_source_value, hn, show 1 ≠ D by omega]
  simp only [recoveryDenominator, map_add, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [hcoord 0 (by decide), hcoord 1 (by decide), hcoord 2 (by decide)]
  ring

theorem recovery_quotient_rep (D r : ℕ) (hD : 5 ≤ D) (hr : 3 ≤ r)
    (t : ℂ) (p : ℙ ℂ (QuotientSpace D r (chosenParameters r)))
    (hp : Represents (quotientCurve D r (chosenParameters r) (some t)) p)
    (hden : MvPolynomial.eval (quotientCoordinateEquiv D r (by omega) hr p.rep)
      (recoveryDenominator D r hD) ≠ 0) :
    Polynomial.eval t (recoveryPolynomial r) ≠ 0 ∧
      rationalRecovery D r hD (quotientCoordinateEquiv D r (by omega) hr p.rep) = t := by
  obtain ⟨c,hc,heq⟩ := hp
  have hcoord : quotientCoordinateEquiv D r (by omega) hr p.rep =
      c • coordinateCurve D r (by omega) (some t) := by
    rw [heq, map_smul]
    rfl
  rw [hcoord, recoveryDenominator_smul, recoveryDenominator_curve] at hden
  have ht := (mul_ne_zero_iff.mp hden).2
  refine ⟨ht, ?_⟩
  rw [hcoord, rationalRecovery_smul D r hD c hc, rationalRecovery_curve D r hD t ht]

theorem recovery_open_point_inverse (D r : ℕ) (hD : 5 ≤ D) (hr : 3 ≤ r)
    (p : ℙ ℂ (QuotientSpace D r (chosenParameters r))) (hp : p ∈ recoveryOpenPoints D r hD hr) :
    let t := rationalRecovery D r hD (quotientCoordinateEquiv D r (by omega) hr p.rep)
    Polynomial.eval t (recoveryPolynomial r) ≠ 0 ∧
      Represents (quotientCurve D r (chosenParameters r) (some t)) p := by
  obtain ⟨⟨s,hs⟩,hden⟩ := hp
  cases s with
  | none =>
    obtain ⟨c,hc,heq⟩ := hs
    have hcoord : quotientCoordinateEquiv D r (by omega) hr p.rep =
        c • coordinateCurve D r (by omega) none := by
      rw [heq, map_smul]
      rfl
    rw [hcoord, recoveryDenominator_smul, recoveryDenominator_infinity, mul_zero] at hden
    exact (hden rfl).elim
  | some t =>
    obtain ⟨ht,hrec⟩ := recovery_quotient_rep D r hD hr t p hs hden
    dsimp only
    rw [hrec]
    exact ⟨ht,hs⟩

theorem recovery_parameter_point (D r : ℕ) (hD : 5 ≤ D) (hr : 3 ≤ r)
    (t : ℂ) (ht : Polynomial.eval t (recoveryPolynomial r) ≠ 0) :
    ∃! p : ℙ ℂ (QuotientSpace D r (chosenParameters r)),
      p ∈ recoveryOpenPoints D r hD hr ∧
        Represents (quotientCurve D r (chosenParameters r) (some t)) p := by
  let v := quotientCurve D r (chosenParameters r) (some t)
  have hv : v ≠ 0 := by
    intro hz
    have he : coordinateCurve D r (by omega) (some t) = 0 := by
      have he := congrArg (quotientCoordinateEquiv D r (by omega) hr) hz
      simpa only [v, quotientCurve, coordinateCurve, quotientCoordinateEquiv_projection, map_zero] using he
    have hd := recoveryDenominator_curve D r hD t
    rw [he] at hd
    apply ht
    rw [← hd]
    simp [recoveryDenominator]
  let p := Projectivization.mk ℂ v hv
  have hp : Represents v p := represents_mk v hv
  refine ⟨p, ⟨?_,hp⟩, ?_⟩
  · refine ⟨⟨some t,hp⟩, ?_⟩
    obtain ⟨c,hc,heq⟩ := hp
    have hcoord : quotientCoordinateEquiv D r (by omega) hr p.rep =
        c • coordinateCurve D r (by omega) (some t) := by
      rw [heq, map_smul]
      rfl
    rw [hcoord, recoveryDenominator_smul, recoveryDenominator_curve]
    exact mul_ne_zero hc ht
  · intro q hq
    exact (represents_iff_eq_mk v hv q).mp hq.2

theorem recovery_open_nonempty (D r : ℕ) (hD : 5 ≤ D) (hr : 3 ≤ r) :
    (recoveryOpenPoints D r hD hr).Nonempty := by
  obtain ⟨t,ht⟩ := recovery_regular_parameter_exists r hr
  obtain ⟨p,hp,_⟩ := recovery_parameter_point D r hD hr t ht
  exact ⟨p,hp.1⟩

theorem recovery_open_dense (D r : ℕ) (hD : 5 ≤ D) (hr : 3 ≤ r) :
    (ProjectiveVariety.mk D (quotientCoordinateEquiv D r (by omega) hr)
      (imageIdeal D r (by omega))).zariskiClosure (recoveryOpenPoints D r hD hr) =
        quotientPoints D r (chosenParameters r) := by
  let X := ProjectiveVariety.mk D (quotientCoordinateEquiv D r (by omega) hr)
    (imageIdeal D r (by omega))
  have hpts : X.points = quotientPoints D r (chosenParameters r) :=
    quotient_image_points D r (by omega) hr
  have hopen : recoveryOpenPoints D r hD hr =
      {p | p ∈ X.points ∧ MvPolynomial.eval (X.coordinates p.rep) (recoveryDenominator D r hD) ≠ 0} := by
    simp only [recoveryOpenPoints, hpts]
    rfl
  change X.zariskiClosure _ = _
  rw [hopen, ← hpts]
  apply principal_open_dense X (quotient_image_admissible D r (by omega) hr)
    (recoveryDenominator D r hD) 1 (recoveryDenominator_homogeneous D r hD)
  obtain ⟨p,hp⟩ := recovery_open_nonempty D r hD hr
  rw [hopen] at hp
  exact ⟨p,hp⟩

theorem recovery_zero_set_closed (D r : ℕ) (hD : 5 ≤ D) (hr : 3 ≤ r) :
    (ProjectiveVariety.mk D (quotientCoordinateEquiv D r (by omega) hr)
      (imageIdeal D r (by omega))).IsClosed
        {p | MvPolynomial.eval (quotientCoordinateEquiv D r (by omega) hr p.rep)
          (recoveryDenominator D r hD) = 0} :=
  homogeneous_zero_set_closed _ _ 1 (recoveryDenominator_homogeneous D r hD)

/-- The maps in both directions are specified: the forward map is the actual
projected polynomial curve, and the inverse is the explicit quotient of linear forms. -/
theorem recovery_open_equiv (D r : ℕ) (hD : 5 ≤ D) (hr : 3 ≤ r) :
    ∃ e : {t : ℂ // Polynomial.eval t (recoveryPolynomial r) ≠ 0} ≃
        {p // p ∈ recoveryOpenPoints D r hD hr},
      (∀ t, Represents (quotientCurve D r (chosenParameters r) (some t.val)) (e t).val) ∧
      (∀ p, (e.symm p).val =
        rationalRecovery D r hD (quotientCoordinateEquiv D r (by omega) hr p.val.rep)) := by
  let V := {t : ℂ // Polynomial.eval t (recoveryPolynomial r) ≠ 0}
  let U := {p // p ∈ recoveryOpenPoints D r hD hr}
  have hex (t : V) := recovery_parameter_point D r hD hr t.val t.property
  let f : V → U := fun t => ⟨(hex t).choose, (hex t).choose_spec.1.1⟩
  have hrep (t : V) : Represents
      (quotientCurve D r (chosenParameters r) (some t.val)) (f t).val :=
    (hex t).choose_spec.1.2
  let g : U → V := fun p => ⟨rationalRecovery D r hD
    (quotientCoordinateEquiv D r (by omega) hr p.val.rep),
      (recovery_open_point_inverse D r hD hr p.val p.property).1⟩
  have hgf (t : V) : g (f t) = t := by
    apply Subtype.ext
    exact (recovery_quotient_rep D r hD hr t.val (f t).val (hrep t) (f t).property.2).2
  have hfg (p : U) : f (g p) = p := by
    apply Subtype.ext
    exact (hex (g p)).unique ⟨(f (g p)).property,hrep (g p)⟩
      ⟨p.property,(recovery_open_point_inverse D r hD hr p.val p.property).2⟩
  exact ⟨⟨f,g,hgf,hfg⟩, hrep, fun _ => rfl⟩

#print axioms recovery_open_equiv
#print axioms recovery_open_dense
#print axioms recovery_open_point_inverse
#print axioms recovery_parameter_point
end NLA.TR27.Paper
