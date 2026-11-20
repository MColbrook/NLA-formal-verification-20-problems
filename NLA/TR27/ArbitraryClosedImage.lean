module

public import NLA.TR27.ArbitraryIntegralImage
public import NLA.TR27.PaperImageGeometry

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper
attribute [local instance] MvPolynomial.gradedAlgebra

theorem parameter_range_eq_cone (D r : ℕ) (hD : 1 ≤ D) (a : Fin r → ℂ) :
    Set.range (parameterHomogeneousMap D r a) =
      {w | w = 0 ∨ ∃ c : ℂ, c ≠ 0 ∧ ∃ t : Option ℂ,
        w = c • parameterCoordinateCurve D r a t} := by
  apply Set.Subset.antisymm
  · rintro w ⟨u,rfl⟩
    by_cases h0 : u 0 = 0
    · have hu : u = u 1 • (![0,1] : Fin 2 → ℂ) := by
        ext j
        fin_cases j <;> simp [Pi.smul_apply,smul_eq_mul,h0]
      rw [hu,parameterHomogeneousMap_smul,parameterHomogeneousMap_infinity D r hD a]
      by_cases h1 : u 1 = 0
      · left
        simp [h1,show D ≠ 0 by omega]
      · exact Or.inr ⟨u 1^D,pow_ne_zero _ h1,none,rfl⟩
    · have hu : u = u 0 • (![1,u 1/u 0] : Fin 2 → ℂ) := by
        ext j
        fin_cases j <;> simp [Pi.smul_apply,smul_eq_mul]
        field_simp
      rw [hu,parameterHomogeneousMap_smul,parameterHomogeneousMap_finite]
      exact Or.inr ⟨u 0^D,pow_ne_zero _ h0,some (u 1/u 0),rfl⟩
  · rintro w (rfl | ⟨c,hc,t,rfl⟩)
    · refine ⟨(0 : ℂ) • (![0,1] : Fin 2 → ℂ), ?_⟩
      rw [parameterHomogeneousMap_smul]
      simp [show D ≠ 0 by omega]
    · obtain ⟨b,hb⟩ := IsAlgClosed.exists_pow_nat_eq c (by omega : 0 < D)
      cases t with
      | none =>
        refine ⟨b • (![0,1] : Fin 2 → ℂ), ?_⟩
        rw [parameterHomogeneousMap_smul,hb,parameterHomogeneousMap_infinity D r hD a]
      | some t =>
        refine ⟨b • (![1,t] : Fin 2 → ℂ), ?_⟩
        rw [parameterHomogeneousMap_smul,hb,parameterHomogeneousMap_finite]

theorem parameter_whole_closed_cone (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) :
    (parameterCoordinateEquiv D r hr a) ⁻¹'
      MvPolynomial.zeroLocus ℂ (parameterImageIdeal D r a) =
      {w | w = 0 ∨ ∃ c : ℂ, c ≠ 0 ∧ ∃ t : Option ℂ,
        w = c • quotientCurve D r (fun i => some (a i)) t} := by
  rw [parameter_zeroLocus_eq_range D r a hD hr hgap,parameter_range_eq_cone D r hD a]
  ext w
  change (_ = 0 ∨ ∃ c : ℂ, c ≠ 0 ∧ ∃ t : Option ℂ,
      parameterCoordinateEquiv D r hr a w = c • parameterCoordinateCurve D r a t) ↔ _
  have hc (t : Option ℂ) : parameterCoordinateEquiv D r hr a
      (quotientCurve D r (fun i => some (a i)) t) = parameterCoordinateCurve D r a t := rfl
  constructor
  · rintro (h | ⟨c,hc0,t,ht⟩)
    · exact Or.inl ((parameterCoordinateEquiv D r hr a).map_eq_zero_iff.mp h)
    · refine Or.inr ⟨c,hc0,t,(parameterCoordinateEquiv D r hr a).injective ?_⟩
      simpa only [map_smul,hc] using ht
  · rintro (rfl | ⟨c,hc0,t,rfl⟩)
    · exact Or.inl (map_zero _)
    · exact Or.inr ⟨c,hc0,t,by rw [map_smul,hc]⟩

theorem parameterHomogeneousCoordinate_isHomogeneous (D r : ℕ) (a : Fin r → ℂ) (j : Fin D) :
    (parameterHomogeneousCoordinate D r a j).IsHomogeneous D := by
  unfold parameterHomogeneousCoordinate
  apply MvPolynomial.IsHomogeneous.add
  · have h := (MvPolynomial.isHomogeneous_C_mul_X_pow (r : ℂ)
      (0 : Fin 2) (D-j.succ.val)).mul
        (MvPolynomial.isHomogeneous_X_pow (R := ℂ) (1 : Fin 2) j.succ.val)
    simpa [Nat.sub_add_cancel (show j.succ.val ≤ D by omega)] using h
  · exact MvPolynomial.isHomogeneous_C_mul_X_pow _ _ _

theorem parameterImageIdeal_isHomogeneous (D r : ℕ) (hD : 1 ≤ D) (a : Fin r → ℂ) :
    (parameterImageIdeal D r a).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin D) ℂ) := by
  have hhom {p : ImageCoordinatePolynomial D} {n : ℕ} (hp : p.IsHomogeneous n) :
      (parameterSubstitution D r a p).IsHomogeneous (D*n) :=
    hp.aeval _ (parameterHomogeneousCoordinate_isHomogeneous D r a)
  have hcomp (p : ImageCoordinatePolynomial D) (n : ℕ) :
      MvPolynomial.homogeneousComponent (D*n) (parameterSubstitution D r a p) =
        parameterSubstitution D r a (MvPolynomial.homogeneousComponent n p) := by
    have hsum : parameterSubstitution D r a p =
        ∑ i ∈ Finset.range (p.totalDegree+1),
          parameterSubstitution D r a (MvPolynomial.homogeneousComponent i p) := by
      rw [← map_sum,MvPolynomial.sum_homogeneousComponent]
    rw [hsum,map_sum]
    simp_rw [MvPolynomial.homogeneousComponent_of_mem
      (hhom (MvPolynomial.homogeneousComponent_isHomogeneous _ _))]
    simp only [Nat.mul_left_cancel_iff (by omega : 0 < D)]
    by_cases hn : n < p.totalDegree+1
    · simp [hn]
    · have hp : p.totalDegree < n := by omega
      simp [hn,MvPolynomial.homogeneousComponent_eq_zero n p hp]
  intro n p hp
  rw [← DirectSum.Decomposition.decompose'_eq,MvPolynomial.decomposition.decompose'_apply]
  change parameterSubstitution D r a (MvPolynomial.homogeneousComponent n p) = 0
  change parameterSubstitution D r a p = 0 at hp
  rw [← hcomp,hp,map_zero]

theorem parameterImageIdeal_isPrime (D r : ℕ) (a : Fin r → ℂ) :
    (parameterImageIdeal D r a).IsPrime :=
  RingHom.ker_isPrime (parameterSubstitution D r a : ImageCoordinatePolynomial D →+* CurveParameterPolynomial)

abbrev parameterImageVariety (D r : ℕ) (hr : 1 ≤ r) (a : Fin r → ℂ) :
    ProjectiveVariety (QuotientSpace D r (fun i => some (a i))) :=
  ProjectiveVariety.mk D (parameterCoordinateEquiv D r hr a) (parameterImageIdeal D r a)

theorem parameter_image_admissible (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) : (parameterImageVariety D r hr a).Admissible := by
  let X := parameterImageVariety D r hr a
  have hc : X.cone = {w | w = 0 ∨ ∃ c : ℂ, c ≠ 0 ∧ ∃ t : Option ℂ,
      w = c • quotientCurve D r (fun i => some (a i)) t} :=
    parameter_whole_closed_cone D r hD hr hgap a
  letI := parameterImageIdeal_isPrime D r a
  refine ⟨parameterImageIdeal_isHomogeneous D r hD a,parameterImageIdeal_isPrime D r a, ?_, ?_, ?_⟩
  · change IsReduced (ImageCoordinatePolynomial D ⧸ parameterImageIdeal D r a)
    infer_instance
  · refine ⟨quotientCurve D r (fun i => some (a i)) (some 0), ?_,
      quotient_curve_nonzero hD hgap _ _⟩
    rw [hc]
    exact Or.inr ⟨1,one_ne_zero,some 0,(one_smul _ _).symm⟩
  · change Submodule.span ℂ X.cone = ⊤
    rw [hc]
    apply top_unique
    rw [← quotient_curve_span D r (fun i => some (a i))]
    apply Submodule.span_mono
    rintro w ⟨t,rfl⟩
    exact Or.inr ⟨1,one_ne_zero,t,(one_smul _ _).symm⟩

theorem parameter_image_points (D r : ℕ) (hD : 1 ≤ D) (hr : 1 ≤ r)
    (hgap : 1+r < D) (a : Fin r → ℂ) :
    (parameterImageVariety D r hr a).points = quotientPoints D r (fun i => some (a i)) := by
  ext p
  change p.rep ∈ (parameterCoordinateEquiv D r hr a) ⁻¹'
    MvPolynomial.zeroLocus ℂ (parameterImageIdeal D r a) ↔ _
  rw [parameter_whole_closed_cone D r hD hr hgap a]
  constructor
  · rintro (hz | ⟨c,hc,t,ht⟩)
    · exact (p.rep_nonzero hz).elim
    · exact ⟨t,c,hc,ht⟩
  · rintro ⟨t,c,hc,ht⟩
    exact Or.inr ⟨c,hc,t,ht⟩

#print axioms parameter_image_admissible
#print axioms parameter_image_points
end NLA.TR27.Paper
