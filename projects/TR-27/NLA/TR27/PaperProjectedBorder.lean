module

public import NLA.TR27.PaperProjectedBorderDefinitions
public import NLA.TR27.PaperImageGeometry
public import NLA.TR27.PaperSourceBorder
public import NLA.TR27.PaperRankOne
public import NLA.TR27.PaperQuotientRank
public import NLA.TR27.AffineBorder

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

abbrev quotientImageVariety (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    ProjectiveVariety (QuotientSpace D r (chosenParameters r)) :=
  ProjectiveVariety.mk D (quotientCoordinateEquiv D r hD hr) (imageIdeal D r hD)

theorem projectedSecant_zero (D r : ℕ) :
    projectedSecant D r 0 = quotientTangent D r (chosenParameters r) := by
  rw [projectedSecant, secantSlope_zero]
  rfl

theorem projectedSecant_difference (D r : ℕ) (t : ℂ) (ht : t ≠ 0) :
    projectedSecant D r t =
      t⁻¹ • (quotientCurve D r (chosenParameters r) (some t) -
        quotientCurve D r (chosenParameters r) (some 0)) := by
  rw [projectedSecant, secantSlope_divided_difference D t ht, map_smul, map_sub]
  rfl

theorem quotientCurve_mem_imageCone (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) (t : Option ℂ) :
    quotientCurve D r (chosenParameters r) t ∈ (quotientImageVariety D r hD hr).cone := by
  change _ ∈ (quotientCoordinateEquiv D r hD hr) ⁻¹' MvPolynomial.zeroLocus ℂ (imageIdeal D r hD)
  rw [quotient_whole_closed_cone D r hD hr]
  exact Or.inr ⟨1, one_ne_zero, t, (one_smul _ _).symm⟩

theorem projectedSecant_coneRank_two (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (t : ℂ) (ht : t ≠ 0) :
    ConeRankAtMost (quotientImageVariety D r hD hr).cone 2 (projectedSecant D r t) := by
  refine ⟨2, le_rfl, ![t⁻¹,-t⁻¹],
    ![quotientCurve D r (chosenParameters r) (some t),
      quotientCurve D r (chosenParameters r) (some 0)], ?_, ?_⟩
  · intro i
    fin_cases i <;> exact quotientCurve_mem_imageCone D r hD hr _
  · rw [projectedSecant_difference D r t ht]
    simp [Fin.sum_univ_two, sub_eq_add_neg]

theorem eval_projectedBorderPolynomial (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (j : Fin D) (t : ℂ) :
    Polynomial.eval t (projectedBorderPolynomial D r hD j) =
      quotientCoordinateEquiv D r hD hr (projectedSecant D r t) j := by
  rw [projectedSecant, quotientCoordinateEquiv_projection]
  by_cases hj : (retainedIndex D hD j).val = 0 <;>
    simp [projectedBorderPolynomial, coordinateProjection, secantSlope, pivotIndex, hj]

theorem eval_projectedBorderSubstitution (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (f : ImageCoordinatePolynomial D) (t : ℂ) :
    Polynomial.eval t (projectedBorderSubstitution D r hD f) =
      MvPolynomial.eval (quotientCoordinateEquiv D r hD hr (projectedSecant D r t)) f := by
  simpa only [projectedBorderSubstitution, Polynomial.coe_aeval_eq_eval,
    eval_projectedBorderPolynomial D r hD hr, MvPolynomial.aeval_eq_eval] using
    (MvPolynomial.comp_aeval_apply (projectedBorderPolynomial D r hD) (Polynomial.aeval t) f)

theorem projected_tangent_affine_border_two (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r) :
    quotientTangent D r (chosenParameters r) ∈
      (quotientImageVariety D r hD hr).affineClosure
        {w | ConeRankAtMost (quotientImageVariety D r hD hr).cone 2 w} := by
  intro f hf
  have hpoly : projectedBorderSubstitution D r hD f = 0 := by
    have hprod : Polynomial.X * projectedBorderSubstitution D r hD f = 0 := by
      apply Polynomial.funext
      intro t
      by_cases ht : t = 0
      · simp [ht]
      · have hz : Polynomial.eval t (projectedBorderSubstitution D r hD f) = 0 := by
          rw [eval_projectedBorderSubstitution D r hD hr]
          exact hf _ ⟨projectedSecant D r t, projectedSecant_coneRank_two D r hD hr t ht, rfl⟩
        simp [hz]
    exact (mul_eq_zero.mp hprod).resolve_left Polynomial.X_ne_zero
  change MvPolynomial.eval (quotientCoordinateEquiv D r hD hr
    (quotientTangent D r (chosenParameters r))) f = 0
  rw [← projectedSecant_zero, ← eval_projectedBorderSubstitution D r hD hr,
    hpoly, Polynomial.eval_zero]

theorem projected_tangent_border_two (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (hgap : 3*r ≤ D) :
    ∃ hv : quotientTangent D r (chosenParameters r) ≠ 0,
      IsLeast {n | Projectivization.mk ℂ _ hv ∈
        (quotientImageVariety D r hD hr).zariskiClosure
          {q | ProjectiveRankAtMost (quotientPoints D r (chosenParameters r)) n q}} 2 ∧
      borderRank (quotientImageVariety D r hD hr) (Projectivization.mk ℂ _ hv) = 2 := by
  let X := quotientImageVariety D r hD hr
  have hX : X.Admissible := quotient_image_admissible D r hD hr
  have hpoints : X.points = quotientPoints D r (chosenParameters r) := quotient_image_points D r hD hr
  have hv := quotient_tangent_nonzero (by omega : 1 ≤ D) (by omega : 1 ≤ r)
    (by omega : r+r < D) (chosenParameters r) (chosenParameters_injective r)
  let p := Projectivization.mk ℂ _ hv
  have hrank := quotient_tangent_rank (by omega : 1 ≤ D) (by omega : 1 ≤ r)
    hgap (chosenParameters r) (chosenParameters_injective r)
  have hout : p ∉ X.points := by
    intro hp
    have hone := (rank_at_most_one_iff_mem X hX p).mpr hp
    rw [hpoints] at hone
    have := hrank.2 hone
    omega
  have hlow : 2 ≤ borderRank X p := border_rank_lower_two X hX p hout
  have hmem : p ∈ X.zariskiClosure {q | ProjectiveRankAtMost X.points 2 q} := by
    exact (projective_affine_border X hX 2 _ hv).mpr
      (projected_tangent_affine_border_two D r hD hr)
  have hupp : borderRank X p ≤ 2 := (rank_minima X hX p).2.2.2 2 |>.mp hmem
  have heq : borderRank X p = 2 := by omega
  refine ⟨hv, ⟨?_, ?_⟩, heq⟩
  · change p ∈ X.zariskiClosure {q | ProjectiveRankAtMost (quotientPoints D r (chosenParameters r)) 2 q}
    rw [← hpoints]
    exact hmem
  · intro n hn
    change p ∈ X.zariskiClosure {q | ProjectiveRankAtMost (quotientPoints D r (chosenParameters r)) n q} at hn
    rw [← hpoints] at hn
    have hle := ((rank_minima X hX p).2.2.2 n).mp hn
    omega

#print axioms projected_tangent_border_two
end NLA.TR27.Paper
