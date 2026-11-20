module

public import NLA.TR27.ArbitraryRecoveryDefinitions
public import NLA.TR27.ArbitraryTraceRecovery
public import NLA.TR27.ArbitraryClosedImage
public import NLA.TR27.PaperHankelRank

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix
namespace NLA.TR27.Paper

theorem parameterLift_curve (D r : ℕ) (hr : 1 ≤ r) (a : Fin r → ℂ) (t : ℂ) :
    parameterLift D r (parameterCoordinateCurve D r a (some t)) =
      curveVector D (some t)+(r : ℂ)⁻¹ • projectionCenter D r (fun i => some (a i)) := by
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [parameterLift,curveVector,parameter_center_zero,hr0]
  · simp only [parameterLift,LinearMap.coe_mk,AddHom.coe_mk,Fin.cases_succ,
      parameterCoordinateCurve,parameterProjection,Pi.add_apply,Pi.smul_apply,
      smul_eq_mul,curveVector,Fin.val_zero,pow_zero]
    field_simp [hr0]
    <;> ring

theorem parameterRecoveryMatrix_eval (D r : ℕ) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ)
    (w : Fin D → ℂ) :
    (parameterRecoveryMatrix D r hD a).map (MvPolynomial.eval w) =
      (centerHankel r a)⁻¹ * sourceHankel (r+1) hD (parameterLift D r w) := by
  rw [parameterRecoveryMatrix,Matrix.map_mul]
  congr 1
  · ext i j
    simp [Matrix.map_map]
  · ext i j
    change MvPolynomial.eval w (parameterPolynomialLift D r ⟨i.val+j.val,by omega⟩) =
      parameterLift D r w ⟨i.val+j.val,by omega⟩
    have he (k : Fin (D+1)) : MvPolynomial.eval w (parameterPolynomialLift D r k) =
        parameterLift D r w k := by
      refine Fin.cases ?_ (fun l => ?_) k <;> simp [parameterPolynomialLift,parameterLift]
    exact he _

theorem parameterRecoveryMatrix_curve (D r : ℕ) (hr : 1 ≤ r) (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) (t : ℂ) :
    (parameterRecoveryMatrix D r hD a).map
      (MvPolynomial.eval (parameterCoordinateCurve D r a (some t))) =
      (r : ℂ)⁻¹ • (1 : Matrix (Fin (r+2)) (Fin (r+2)) ℂ)+
        Matrix.vecMulVec ((centerHankel r a)⁻¹ *ᵥ (fun i : Fin (r+2) => t^i.val))
          (fun i : Fin (r+2) => t^i.val) := by
  rw [parameterRecoveryMatrix_eval,parameterLift_curve D r hr a]
  have hsum : sourceHankel (r+1) hD
      (curveVector D (some t)+(r : ℂ)⁻¹ • projectionCenter D r (fun i => some (a i))) =
      sourceHankel (r+1) hD (curveVector D (some t))+
        (r : ℂ)⁻¹ • sourceHankel (r+1) hD (projectionCenter D r (fun i => some (a i))) := by
    rfl
  rw [hsum,centerHankel_coordinates,sourceHankel_curve,mul_add,Matrix.mul_smul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (centerHankel_det_ne_zero r a ha ha0)),
    Matrix.mul_vecMulVec]
  exact add_comm _ _

theorem vecMulVec_trace_square {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    Matrix.vecMulVec u v * Matrix.vecMulVec u v =
      (Matrix.vecMulVec u v).trace • Matrix.vecMulVec u v := by
  rw [Matrix.vecMulVec_mul_vecMulVec,Matrix.vecMulVec_smul,Matrix.trace_vecMulVec,
    dotProduct_comm u v]

theorem parameterAlphaPolynomial_eval (D r : ℕ) (hr : 1 ≤ r) (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) (t : ℂ) :
    (parameterAlphaPolynomial D r hD a).eval t =
      (Matrix.vecMulVec ((centerHankel r a)⁻¹ *ᵥ (fun i : Fin (r+2) => t^i.val))
        (fun i : Fin (r+2) => t^i.val)).trace := by
  have hev (j : Fin D) : (parameterAffinePolynomial D r a j).eval t =
      parameterCoordinateCurve D r a (some t) j := by
    simp [parameterAffinePolynomial,parameterCoordinateCurve,parameterProjection,curveVector]
  have heval := MvPolynomial.comp_aeval_apply (parameterAffinePolynomial D r a)
    (Polynomial.aeval t) (parameterRecoveryMatrix D r hD a).trace
  have htr : MvPolynomial.eval (parameterCoordinateCurve D r a (some t))
      (parameterRecoveryMatrix D r hD a).trace =
      ((parameterRecoveryMatrix D r hD a).map
        (MvPolynomial.eval (parameterCoordinateCurve D r a (some t)))).trace :=
    AddMonoidHom.map_trace _ _
  simp only [parameterAlphaPolynomial,Polynomial.eval_sub,Polynomial.eval_C]
  rw [show Polynomial.eval t (MvPolynomial.aeval (parameterAffinePolynomial D r a)
      (parameterRecoveryMatrix D r hD a).trace) =
      MvPolynomial.eval (parameterCoordinateCurve D r a (some t))
        (parameterRecoveryMatrix D r hD a).trace by
    simpa only [Polynomial.coe_aeval_eq_eval,hev,MvPolynomial.aeval_eq_eval] using heval]
  rw [htr,parameterRecoveryMatrix_curve D r hr hD a ha ha0 t]
  simp only [Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,smul_eq_mul]
  ring

/-- Both branches of the rational formula agree with the coefficient of the
identity in the literal Hankel matrix, and have a nonzero denominator away
from the finite exceptional set. -/
theorem parameter_beta_recovery (D r : ℕ) (hr : 1 ≤ r) (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) (t : ℂ)
    (ht : (parameterRecoveryException D r hD a).eval t ≠ 0) :
    let w := parameterCoordinateCurve D r a (some t)
    MvPolynomial.eval w (parameterBetaDenominator D r hD a) ≠ 0 ∧
      MvPolynomial.eval w (parameterBetaNumerator D r hD a) =
        (r : ℂ)⁻¹*MvPolynomial.eval w (parameterBetaDenominator D r hD a) := by
  let w := parameterCoordinateCurve D r a (some t)
  change MvPolynomial.eval w (parameterBetaDenominator D r hD a) ≠ 0 ∧
    MvPolynomial.eval w (parameterBetaNumerator D r hD a) =
      (r : ℂ)⁻¹*MvPolynomial.eval w (parameterBetaDenominator D r hD a)
  let R := Matrix.vecMulVec ((centerHankel r a)⁻¹ *ᵥ (fun i : Fin (r+2) => t^i.val))
    (fun i : Fin (r+2) => t^i.val)
  let α := R.trace
  let n : ℂ := (r+2 : ℕ)
  let K := (r : ℂ)⁻¹ • (1 : Matrix (Fin (r+2)) (Fin (r+2)) ℂ)+R
  have heval (j : ℕ) : MvPolynomial.eval w ((parameterRecoveryMatrix D r hD a)^j).trace =
      (K^j).trace := by
    rw [AddMonoidHom.map_trace,Matrix.map_pow,parameterRecoveryMatrix_curve D r hr hD a ha ha0 t]
  have heval1 : MvPolynomial.eval w (parameterRecoveryMatrix D r hD a).trace = K.trace := by
    simpa only [pow_one] using heval 1
  have hsq : R*R = α • R := vecMulVec_trace_square _ _
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn0 : n ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : n-1 ≠ 0 := sub_ne_zero.mpr (by dsimp [n]; exact_mod_cast (show r+2 ≠ 1 by omega))
  have hn2 : n-2 ≠ 0 := sub_ne_zero.mpr (by dsimp [n]; exact_mod_cast (show r+2 ≠ 2 by omega))
  have hnr : n-2 = (r : ℂ) := by dsimp [n]; push_cast; ring
  by_cases hz : parameterAlphaPolynomial D r hD a = 0
  · have hα : α = 0 := by
      have he := parameterAlphaPolynomial_eval D r hr hD a ha ha0 t
      rw [hz,Polynomial.eval_zero] at he
      exact he.symm
    simp only [parameterBetaNumerator,parameterBetaDenominator,if_pos hz,
      MvPolynomial.eval_C,heval1]
    have hT : K.trace = n*(r : ℂ)⁻¹ := by
      simp only [K,Matrix.trace_add,Matrix.trace_smul,Matrix.trace_one,Fintype.card_fin,
        smul_eq_mul,show R.trace = 0 from hα,add_zero]
      ring
    exact ⟨hn0,by rw [hT]; ring⟩
  · have hα : α ≠ 0 := by
      have he := parameterAlphaPolynomial_eval D r hr hD a ha ha0 t
      simpa only [parameterRecoveryException,if_neg hz,he] using ht
    obtain ⟨hT,hV,hW⟩ := scalar_rank_one_trace_identities R α (r : ℂ)⁻¹ rfl hsq
    simp only [Fintype.card_fin] at hT hV hW
    change K.trace = n*(r : ℂ)⁻¹+α at hT
    change n*(K^2).trace-K.trace^2 = (n-1)*α^2 at hV
    change n^2*(K^3).trace-3*n*K.trace*(K^2).trace+2*K.trace^3 =
      (n-1)*(n-2)*α^3 at hW
    simp only [parameterBetaNumerator,parameterBetaDenominator,if_neg hz,
      parameterRecoveryV,parameterRecoveryW,map_mul,map_sub,map_add,map_pow,
      MvPolynomial.eval_C,heval1,heval]
    change n*(r : ℂ)*(n*(K^2).trace-K.trace^2) ≠ 0 ∧
      K.trace*(r : ℂ)*(n*(K^2).trace-K.trace^2)-
          (n^2*(K^3).trace-3*n*K.trace*(K^2).trace+2*K.trace^3) =
        (r : ℂ)⁻¹*(n*(r : ℂ)*(n*(K^2).trace-K.trace^2))
    rw [hV,hW,hT]
    refine ⟨mul_ne_zero (mul_ne_zero hn0 hr0) (mul_ne_zero hn1 (pow_ne_zero _ hα)), ?_⟩
    rw [hnr]
    field_simp [hr0]
    <;> ring

theorem parameter_rational_recovery (D r : ℕ) (hr : 1 ≤ r) (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) (t : ℂ)
    (ht : (parameterRecoveryException D r hD a).eval t ≠ 0) :
    let w := parameterCoordinateCurve D r a (some t)
    MvPolynomial.eval w (parameterRecoveryDenominator D r hD a) ≠ 0 ∧
      MvPolynomial.eval w (parameterRecoveryNumerator D r hD hr a)/
        MvPolynomial.eval w (parameterRecoveryDenominator D r hD a) = t := by
  obtain ⟨hden,heq⟩ := parameter_beta_recovery D r hr hD a ha ha0 t ht
  dsimp only at hden heq ⊢
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hv : parameterCoordinateCurve D r a (some t) ⟨0,by omega⟩ = (r : ℂ)*t+
      projectionCenter D r (fun i => some (a i)) ⟨1,by omega⟩ := by
    simp [parameterCoordinateCurve,parameterProjection,curveVector]
  simp only [parameterRecoveryNumerator,parameterRecoveryDenominator,map_mul,map_sub,
    MvPolynomial.eval_C,MvPolynomial.eval_X,heq]
  rw [hv]
  constructor
  · exact mul_ne_zero hr0 (mul_ne_zero (inv_ne_zero hr0) hden)
  · field_simp [hr0,hden]
    <;> ring

theorem parameter_recovery_exception_finite (D r : ℕ) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) :
    parameterRecoveryException D r hD a ≠ 0 ∧
      Set.Finite {t : ℂ | (parameterRecoveryException D r hD a).eval t = 0} := by
  have h : parameterRecoveryException D r hD a ≠ 0 := by
    unfold parameterRecoveryException
    split_ifs with h
    · exact one_ne_zero
    · exact h
  exact ⟨h,Polynomial.finite_setOfPred_isRoot h⟩

#print axioms parameter_rational_recovery
#print axioms parameter_recovery_exception_finite
end NLA.TR27.Paper
