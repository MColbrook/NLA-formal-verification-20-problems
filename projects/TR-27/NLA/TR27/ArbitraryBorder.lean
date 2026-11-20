module

public import NLA.TR27.ArbitraryClosedImage
public import NLA.TR27.ArbitraryParametersSolution
public import NLA.TR27.AffineBorder
public import NLA.TR27.PaperRankOne

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

def parameterSecantSubstitution (D r : ℕ) : ImageCoordinatePolynomial D →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun j : Fin D => Polynomial.C (r : ℂ)*Polynomial.X^j.val)

theorem parameterCurve_mem_cone (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) (t : Option ℂ) :
    quotientCurve D r (fun i => some (a i)) t ∈ (parameterImageVariety D r hr a).cone := by
  change _ ∈ (parameterCoordinateEquiv D r hr a) ⁻¹'
    MvPolynomial.zeroLocus ℂ (parameterImageIdeal D r a)
  rw [parameter_whole_closed_cone D r hD hr hgap a]
  exact Or.inr ⟨1,one_ne_zero,t,(one_smul _ _).symm⟩

theorem parameterSecant_coneRank_two (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) (t : ℂ) (ht : t ≠ 0) :
    ConeRankAtMost (parameterImageVariety D r hr a).cone 2
      (parameterSecant D r (fun i => some (a i)) t) := by
  refine ⟨2,le_rfl,![t⁻¹,-t⁻¹],
    ![quotientCurve D r (fun i => some (a i)) (some t),
      quotientCurve D r (fun i => some (a i)) (some 0)], ?_, ?_⟩
  · intro i
    fin_cases i <;> exact parameterCurve_mem_cone D r hD hr hgap a _
  · rw [parameterSecant_difference D r _ t ht]
    simp [Fin.sum_univ_two,sub_eq_add_neg]

theorem eval_parameterSecantSubstitution (D r : ℕ) (hr : 1 ≤ r)
    (a : Fin r → ℂ) (f : ImageCoordinatePolynomial D) (t : ℂ) :
    Polynomial.eval t (parameterSecantSubstitution D r f) =
      MvPolynomial.eval (parameterCoordinateEquiv D r hr a
        (parameterSecant D r (fun i => some (a i)) t)) f := by
  have he (j : Fin D) : Polynomial.eval t (Polynomial.C (r : ℂ)*Polynomial.X^j.val) =
      parameterCoordinateEquiv D r hr a
        (parameterSecant D r (fun i => some (a i)) t) j := by
    rw [parameterSecant,parameterCoordinateEquiv_projection]
    simp [parameterProjection,secantSlope]
  have hcomp := MvPolynomial.comp_aeval_apply
    (fun j : Fin D => Polynomial.C (r : ℂ)*Polynomial.X^j.val) (Polynomial.aeval t) f
  have hcomp' : Polynomial.eval t (parameterSecantSubstitution D r f) =
      MvPolynomial.eval (fun j : Fin D =>
        Polynomial.eval t (Polynomial.C (r : ℂ)*Polynomial.X^j.val)) f := by
    simpa only [parameterSecantSubstitution,Polynomial.coe_aeval_eq_eval,
      MvPolynomial.aeval_eq_eval] using hcomp
  rw [funext he] at hcomp'
  exact hcomp'

theorem parameter_tangent_affine_border_two (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) :
    quotientTangent D r (fun i => some (a i)) ∈
      (parameterImageVariety D r hr a).affineClosure
        {w | ConeRankAtMost (parameterImageVariety D r hr a).cone 2 w} := by
  intro f hf
  have hpoly : parameterSecantSubstitution D r f = 0 := by
    have hprod : Polynomial.X*parameterSecantSubstitution D r f = 0 := by
      apply Polynomial.funext
      intro t
      by_cases ht : t = 0
      · simp [ht]
      · have hz : Polynomial.eval t (parameterSecantSubstitution D r f) = 0 := by
          rw [eval_parameterSecantSubstitution D r hr a]
          exact hf _ ⟨parameterSecant D r (fun i => some (a i)) t,
            parameterSecant_coneRank_two D r hD hr hgap a t ht,rfl⟩
        simp [hz]
    exact (mul_eq_zero.mp hprod).resolve_left Polynomial.X_ne_zero
  change MvPolynomial.eval (parameterCoordinateEquiv D r hr a
    (quotientTangent D r (fun i => some (a i)))) f = 0
  rw [← parameterSecant_zero,← eval_parameterSecantSubstitution D r hr a,
    hpoly,Polynomial.eval_zero]

theorem parameter_tangent_border_two (D r : ℕ) (hr : 3 ≤ r) (hgap : 3*r ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) :
    ∃ hv : quotientTangent D r (fun i => some (a i)) ≠ 0,
      borderRank (parameterImageVariety D r (by omega) a) (Projectivization.mk ℂ _ hv) = 2 := by
  let X := parameterImageVariety D r (by omega) a
  have hX : X.Admissible := parameter_image_admissible D r (by omega) (by omega) (by omega) a
  have hpoints : X.points = quotientPoints D r (fun i => some (a i)) :=
    parameter_image_points D r (by omega) (by omega) (by omega) a
  have hai : Function.Injective (fun i => some (a i)) := by
    intro i j hij
    exact ha (Option.some.inj hij)
  have hv := quotient_tangent_nonzero (by omega : 1 ≤ D) (by omega : 1 ≤ r)
    (by omega : r+r < D) (fun i => some (a i)) hai
  let p := Projectivization.mk ℂ _ hv
  have hrank := quotient_tangent_rank (by omega : 1 ≤ D) (by omega : 1 ≤ r)
    hgap (fun i => some (a i)) hai
  have hout : p ∉ X.points := by
    intro hp
    have hone := (rank_at_most_one_iff_mem X hX p).mpr hp
    rw [hpoints] at hone
    have := hrank.2 hone
    omega
  have hlow : 2 ≤ borderRank X p := border_rank_lower_two X hX p hout
  have hmem : p ∈ X.zariskiClosure {q | ProjectiveRankAtMost X.points 2 q} :=
    (projective_affine_border X hX 2 _ hv).mpr
      (parameter_tangent_affine_border_two D r (by omega) (by omega) (by omega) a)
  have hupp : borderRank X p ≤ 2 := (rank_minima X hX p).2.2.2 2 |>.mp hmem
  have heq : borderRank X p = 2 := by omega
  exact ⟨hv,heq⟩

#print axioms parameter_tangent_border_two
end NLA.TR27.Paper
