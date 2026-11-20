module

public import NLA.TR27.ArbitraryBirationalDefinitions
public import NLA.TR27.ArbitraryRecoveryHomogeneous
public import NLA.TR27.ArbitraryParametersSolution

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

theorem parameter_denominator_regular (D r : ℕ) (hr : 1 ≤ r) (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) (t : ℂ)
    (hden : MvPolynomial.eval (parameterCoordinateCurve D r a (some t))
      (parameterRecoveryDenominator D r hD a) ≠ 0) :
    (parameterRecoveryException D r hD a).eval t ≠ 0 := by
  intro ht
  by_cases hz : parameterAlphaPolynomial D r hD a = 0
  · simpa only [parameterRecoveryException,if_pos hz,Polynomial.eval_one,one_ne_zero] using ht
  let R := Matrix.vecMulVec ((centerHankel r a)⁻¹ *ᵥ (fun i : Fin (r+2) => t^i.val))
    (fun i : Fin (r+2) => t^i.val)
  let n : ℂ := (r+2 : ℕ)
  let K := (r : ℂ)⁻¹ • (1 : Matrix (Fin (r+2)) (Fin (r+2)) ℂ)+R
  have hα : R.trace = 0 := by
    have he := parameterAlphaPolynomial_eval D r hr hD a ha ha0 t
    simpa only [parameterRecoveryException,if_neg hz,he] using ht
  have heval (j : ℕ) : MvPolynomial.eval (parameterCoordinateCurve D r a (some t))
      ((parameterRecoveryMatrix D r hD a)^j).trace = (K^j).trace := by
    rw [AddMonoidHom.map_trace,Matrix.map_pow,parameterRecoveryMatrix_curve D r hr hD a ha ha0 t]
  have heval1 : MvPolynomial.eval (parameterCoordinateCurve D r a (some t))
      (parameterRecoveryMatrix D r hD a).trace = K.trace := by
    simpa only [pow_one] using heval 1
  obtain ⟨hT,hV,hW⟩ := scalar_rank_one_trace_identities R 0 (r : ℂ)⁻¹ hα
    (by
      rw [← hα]
      exact vecMulVec_trace_square
        ((centerHankel r a)⁻¹ *ᵥ (fun i : Fin (r+2) => t^i.val))
        (fun i : Fin (r+2) => t^i.val))
  simp only [Fintype.card_fin] at hV hW
  change n*(K^2).trace-K.trace^2 = _ at hV
  change n^2*(K^3).trace-3*n*K.trace*(K^2).trace+2*K.trace^3 = _ at hW
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0),zero_pow (by decide : (3 : ℕ) ≠ 0),
    mul_zero] at hV hW
  apply hden
  simp only [parameterRecoveryDenominator,parameterBetaNumerator,if_neg hz,
    parameterRecoveryV,parameterRecoveryW,map_mul,map_sub,map_add,map_pow,
    MvPolynomial.eval_C,heval,heval1]
  change (r : ℂ)*(K.trace*(r : ℂ)*(n*(K^2).trace-K.trace^2)-
    (n^2*(K^3).trace-3*n*K.trace*(K^2).trace+2*K.trace^3)) = 0
  rw [hV,hW]
  ring

theorem parameter_birational_exception_nonzero (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) :
    parameterBirationalException D r hr hD a ≠ 0 := by
  apply mul_ne_zero (parameter_recovery_exception_finite D r hD a).1
  intro hz
  have he := congrArg (fun p : Polynomial ℂ => p.coeff 1) hz
  simp [parameterAffinePolynomial] at he
  omega

theorem parameter_birational_homogeneous (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) :
    ∃ d : ℕ, (parameterBirationalNumerator D r hr hD a).IsHomogeneous d ∧
      (parameterBirationalDenominator D r hr hD a).IsHomogeneous d := by
  obtain ⟨d,hN,hDen⟩ := parameter_recovery_homogeneous D r hr hD a
  exact ⟨d+1,hN.mul (MvPolynomial.isHomogeneous_X _ _),
    hDen.mul (MvPolynomial.isHomogeneous_X _ _)⟩

theorem parameter_birational_curve (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) (t : ℂ)
    (ht : (parameterBirationalException D r hr hD a).eval t ≠ 0) :
    let w := parameterCoordinateCurve D r a (some t)
    MvPolynomial.eval w (parameterBirationalDenominator D r hr hD a) ≠ 0 ∧
      parameterBirationalRecovery D r hr hD a w = t := by
  have hev : (parameterAffinePolynomial D r a ⟨0,by omega⟩).eval t =
      parameterCoordinateCurve D r a (some t) ⟨0,by omega⟩ := by
    simp [parameterAffinePolynomial,parameterCoordinateCurve,parameterProjection,curveVector]
  rw [parameterBirationalException,Polynomial.eval_mul,hev] at ht
  obtain ⟨hden,hrec⟩ := parameter_rational_recovery D r hr hD a ha ha0 t
    (mul_ne_zero_iff.mp ht).1
  dsimp only at hden hrec ⊢
  simp only [parameterBirationalDenominator,parameterBirationalNumerator,
    parameterBirationalRecovery,map_mul,MvPolynomial.eval_X]
  exact ⟨mul_ne_zero hden (mul_ne_zero_iff.mp ht).2,
    (mul_div_mul_right _ _ (mul_ne_zero_iff.mp ht).2).trans hrec⟩

theorem parameter_birational_quotient_rep (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) (t : ℂ)
    (p : ℙ ℂ (QuotientSpace D r (fun i => some (a i))))
    (hp : Represents (quotientCurve D r (fun i => some (a i)) (some t)) p)
    (ht : (parameterBirationalException D r hr hD a).eval t ≠ 0) :
    p ∈ parameterBirationalOpen D r hr hD a ∧
      parameterBirationalRecovery D r hr hD a (parameterCoordinateEquiv D r hr a p.rep) = t := by
  obtain ⟨d,hN,hDen⟩ := parameter_birational_homogeneous D r hr hD a
  obtain ⟨hden,hrec⟩ := parameter_birational_curve D r hr hD a ha ha0 t ht
  obtain ⟨c,hc,heq⟩ := hp
  have he : parameterCoordinateEquiv D r hr a p.rep =
      c • parameterCoordinateCurve D r a (some t) := by
    rw [heq,map_smul,quotientCurve,parameterCoordinateEquiv_projection]
    rfl
  refine ⟨⟨⟨some t,c,hc,heq⟩, ?_⟩, ?_⟩
  · rw [he,homogeneous_eval_smul _ d hDen]
    exact mul_ne_zero (pow_ne_zero _ hc) hden
  · unfold parameterBirationalRecovery
    rw [he,homogeneous_eval_smul _ d hN,homogeneous_eval_smul _ d hDen]
    exact (mul_div_mul_left _ _ (pow_ne_zero d hc)).trans hrec

theorem parameter_birational_parameter (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0)
    (p : ℙ ℂ (QuotientSpace D r (fun i => some (a i))))
    (hp : p ∈ parameterBirationalOpen D r hr hD a) :
    ∃ t : ℂ, (parameterBirationalException D r hr hD a).eval t ≠ 0 ∧
      Represents (quotientCurve D r (fun i => some (a i)) (some t)) p ∧
      parameterBirationalRecovery D r hr hD a (parameterCoordinateEquiv D r hr a p.rep) = t := by
  obtain ⟨d,hN,hDen⟩ := parameter_birational_homogeneous D r hr hD a
  obtain ⟨u,c,hc,heq⟩ := hp.1
  have he : parameterCoordinateEquiv D r hr a p.rep =
      c • parameterCoordinateCurve D r a u := by
    rw [heq,map_smul,quotientCurve,parameterCoordinateEquiv_projection]
    rfl
  have hnon : MvPolynomial.eval (parameterCoordinateCurve D r a u)
      (parameterBirationalDenominator D r hr hD a) ≠ 0 := by
    intro hz
    apply hp.2
    rw [he,homogeneous_eval_smul _ d hDen,hz,mul_zero]
  cases u with
  | none =>
    have hinf : parameterCoordinateCurve D r a none ⟨0,by omega⟩ = 0 := by
      have hn : (1 : ℕ) ≠ D := by omega
      have h0 : (0 : ℕ) ≠ D := by omega
      simp [parameterCoordinateCurve,parameterProjection,curveVector,hn,h0]
    exact (hnon (by simp [parameterBirationalDenominator,hinf])).elim
  | some t =>
    have hpair := mul_ne_zero_iff.mp (show MvPolynomial.eval (parameterCoordinateCurve D r a (some t))
      (parameterRecoveryDenominator D r hD a) *
      parameterCoordinateCurve D r a (some t) ⟨0,by omega⟩ ≠ 0 by
        simpa only [parameterBirationalDenominator,map_mul,MvPolynomial.eval_X] using hnon)
    have hreg := parameter_denominator_regular D r hr hD a ha ha0 t hpair.1
    have hfirst : (parameterAffinePolynomial D r a ⟨0,by omega⟩).eval t ≠ 0 := by
      simpa [parameterAffinePolynomial,parameterCoordinateCurve,parameterProjection,curveVector] using hpair.2
    have ht : (parameterBirationalException D r hr hD a).eval t ≠ 0 := by
      simpa only [parameterBirationalException,Polynomial.eval_mul] using mul_ne_zero hreg hfirst
    exact ⟨t,ht,⟨c,hc,heq⟩,
      (parameter_birational_quotient_rep D r hr hD a ha ha0 t p ⟨c,hc,heq⟩ ht).2⟩

theorem parameter_birational_nonempty (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) : (parameterBirationalOpen D r hr hD a).Nonempty := by
  have hex : ∃ t : ℂ, (parameterBirationalException D r hr hD a).eval t ≠ 0 := by
    by_contra h
    push Not at h
    apply parameter_birational_exception_nonzero D r hr hD a
    apply Polynomial.funext
    intro t
    simp only [h,Polynomial.eval_zero]
  obtain ⟨t,ht⟩ := hex
  have hv := quotient_curve_nonzero (by omega : 1 ≤ D) (by omega : 1+r < D)
    (fun i => some (a i)) (some t)
  let p := Projectivization.mk ℂ _ hv
  exact ⟨p,(parameter_birational_quotient_rep D r hr hD a ha ha0 t p (represents_mk _ _) ht).1⟩

theorem parameter_birational_dense (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) :
    (parameterImageVariety D r hr a).zariskiClosure (parameterBirationalOpen D r hr hD a) =
      quotientPoints D r (fun i => some (a i)) := by
  let X := parameterImageVariety D r hr a
  have hX := parameter_image_admissible D r (by omega) hr (by omega) a
  have hpts : X.points = quotientPoints D r (fun i => some (a i)) :=
    parameter_image_points D r (by omega) hr (by omega) a
  obtain ⟨d,hN,hDen⟩ := parameter_birational_homogeneous D r hr hD a
  have hopen : parameterBirationalOpen D r hr hD a =
      {p | p ∈ X.points ∧ MvPolynomial.eval (X.coordinates p.rep)
        (parameterBirationalDenominator D r hr hD a) ≠ 0} := by
    simp only [parameterBirationalOpen,hpts]
    rfl
  rw [hopen,← hpts]
  apply principal_open_dense X hX _ d hDen
  obtain ⟨p,hp⟩ := parameter_birational_nonempty D r hr hD a ha ha0
  rw [hopen] at hp
  exact ⟨p,hp⟩

theorem parameter_birational_equiv (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) :
    ∃ e : {t : ℂ // (parameterBirationalException D r hr hD a).eval t ≠ 0} ≃
        {p // p ∈ parameterBirationalOpen D r hr hD a},
      (∀ t, Represents (quotientCurve D r (fun i => some (a i)) (some t.val)) (e t).val) ∧
      (∀ p, (e.symm p).val = parameterBirationalRecovery D r hr hD a
        (parameterCoordinateEquiv D r hr a p.val.rep)) := by
  let V := {t : ℂ // (parameterBirationalException D r hr hD a).eval t ≠ 0}
  let U := {p // p ∈ parameterBirationalOpen D r hr hD a}
  have hv (t : V) := quotient_curve_nonzero (by omega : 1 ≤ D) (by omega : 1+r < D)
    (fun i => some (a i)) (some t.val)
  let f : V → U := fun t => ⟨Projectivization.mk ℂ _ (hv t),
    (parameter_birational_quotient_rep D r hr hD a ha ha0 t.val _ (represents_mk _ _) t.property).1⟩
  have hf (t : V) : Represents
      (quotientCurve D r (fun i => some (a i)) (some t.val)) (f t).val := represents_mk _ _
  have hpar (p : U) := parameter_birational_parameter D r hr hD a ha ha0 p.val p.property
  let g : U → V := fun p => ⟨(hpar p).choose,(hpar p).choose_spec.1⟩
  have hg (p : U) : Represents (quotientCurve D r (fun i => some (a i)) (some (g p).val)) p.val :=
    (hpar p).choose_spec.2.1
  have hval (p : U) : parameterBirationalRecovery D r hr hD a
      (parameterCoordinateEquiv D r hr a p.val.rep) = (g p).val := (hpar p).choose_spec.2.2
  have hgf (t : V) : g (f t) = t := by
    apply Subtype.ext
    rw [← hval]
    exact (parameter_birational_quotient_rep D r hr hD a ha ha0 t.val (f t).val (hf t) t.property).2
  have hfg (p : U) : f (g p) = p := by
    apply Subtype.ext
    exact ((represents_iff_eq_mk _ (hv (g p)) _).mp (hf (g p))).trans
      ((represents_iff_eq_mk _ (hv (g p)) _).mp (hg p)).symm
  exact ⟨⟨f,g,hgf,hfg⟩,hf,fun p => (hval p).symm⟩

#print axioms parameter_birational_dense
#print axioms parameter_birational_equiv
end NLA.TR27.Paper
