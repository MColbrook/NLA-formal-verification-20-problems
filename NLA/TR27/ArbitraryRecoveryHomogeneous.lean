module

public import NLA.TR27.ArbitraryRecovery
public import NLA.TR27.PaperPrincipalOpen

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

private theorem polynomial_trace_homogeneous {n d : ℕ}
    (M : Matrix (Fin n) (Fin n) (ImageCoordinatePolynomial n))
    (hM : ∀ i j, (M i j).IsHomogeneous d) : M.trace.IsHomogeneous d :=
  MvPolynomial.IsHomogeneous.sum Finset.univ (fun i => M i i) d (fun i _ => hM i i)

private theorem polynomial_matrix_mul_homogeneous {ι κ ν σ : Type*} [Fintype κ]
    (A : Matrix ι κ (MvPolynomial σ ℂ)) (B : Matrix κ ν (MvPolynomial σ ℂ))
    (d e : ℕ) (hA : ∀ i j, (A i j).IsHomogeneous d)
    (hB : ∀ i j, (B i j).IsHomogeneous e) (i : ι) (j : ν) :
    ((A*B) i j).IsHomogeneous (d+e) :=
  MvPolynomial.IsHomogeneous.sum Finset.univ (fun k => A i k*B k j) (d+e)
    (fun k _ => (hA i k).mul (hB k j))

private theorem parameter_matrix_homogeneous (D r : ℕ) (hD : 2*(r+1) ≤ D)
    (a : Fin r → ℂ) : ∀ i j, (parameterRecoveryMatrix D r hD a i j).IsHomogeneous 1 := by
  intro i j
  unfold parameterRecoveryMatrix
  apply polynomial_matrix_mul_homogeneous _ _ 0 1
  · intro i j
    exact MvPolynomial.isHomogeneous_C _ _
  · intro i j
    change (parameterPolynomialLift D r ⟨i.val+j.val,by omega⟩).IsHomogeneous 1
    generalize (⟨i.val+j.val,by omega⟩ : Fin (D+1)) = k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact MvPolynomial.isHomogeneous_zero _ _ _
    · exact MvPolynomial.isHomogeneous_C_mul_X _ _

private theorem polynomial_trace_homogeneous' {n D d : ℕ}
    (M : Matrix (Fin n) (Fin n) (ImageCoordinatePolynomial D))
    (hM : ∀ i j, (M i j).IsHomogeneous d) : M.trace.IsHomogeneous d :=
  MvPolynomial.IsHomogeneous.sum Finset.univ (fun i => M i i) d (fun i _ => hM i i)

theorem parameter_recovery_homogeneous (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) :
    ∃ d : ℕ, (parameterRecoveryNumerator D r hD hr a).IsHomogeneous d ∧
      (parameterRecoveryDenominator D r hD a).IsHomogeneous d := by
  let M := parameterRecoveryMatrix D r hD a
  have hM : ∀ i j, (M i j).IsHomogeneous 1 := parameter_matrix_homogeneous D r hD a
  have hM2 : ∀ i j, ((M^2) i j).IsHomogeneous 2 := by
    rw [pow_two]
    exact polynomial_matrix_mul_homogeneous _ _ 1 1 hM hM
  have hM3 : ∀ i j, ((M^3) i j).IsHomogeneous 3 := by
    rw [show (3 : ℕ) = 2+1 by rfl,pow_succ]
    exact polynomial_matrix_mul_homogeneous _ _ 2 1 hM2 hM
  have hT := polynomial_trace_homogeneous' M hM
  have hS := polynomial_trace_homogeneous' (M^2) hM2
  have hU := polynomial_trace_homogeneous' (M^3) hM3
  have hV : (parameterRecoveryV D r hD a).IsHomogeneous 2 :=
    (hS.C_mul _).sub (hT.pow 2)
  have hW : (parameterRecoveryW D r hD a).IsHomogeneous 3 :=
    ((hU.C_mul _).sub ((hT.C_mul _).mul hS)).add ((hT.pow 3).C_mul _)
  by_cases hz : parameterAlphaPolynomial D r hD a = 0
  · refine ⟨1, ?_, ?_⟩
    · unfold parameterRecoveryNumerator parameterBetaNumerator parameterBetaDenominator
      simp only [if_pos hz]
      exact ((MvPolynomial.isHomogeneous_C_mul_X _ _).mul
        (MvPolynomial.isHomogeneous_C _ _)).sub (hT.C_mul _)
    · unfold parameterRecoveryDenominator parameterBetaNumerator
      simp only [if_pos hz]
      exact hT.C_mul _
  · have hBN : (parameterBetaNumerator D r hD a).IsHomogeneous 3 := by
      unfold parameterBetaNumerator
      simp only [if_neg hz]
      exact ((hT.mul (MvPolynomial.isHomogeneous_C _ _)).mul hV).sub hW
    have hBD : (parameterBetaDenominator D r hD a).IsHomogeneous 2 := by
      unfold parameterBetaDenominator
      simp only [if_neg hz]
      exact hV.C_mul _
    exact ⟨3,((MvPolynomial.isHomogeneous_C_mul_X _ _).mul hBD).sub (hBN.C_mul _),
      hBN.C_mul _⟩

theorem parameter_projective_rational_recovery (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (ha : Function.Injective a)
    (ha0 : ∀ i, a i ≠ 0) (t : ℂ) (p : ℙ ℂ (Fin D → ℂ))
    (hp : Represents (parameterCoordinateCurve D r a (some t)) p)
    (ht : (parameterRecoveryException D r hD a).eval t ≠ 0) :
    MvPolynomial.eval p.rep (parameterRecoveryDenominator D r hD a) ≠ 0 ∧
      MvPolynomial.eval p.rep (parameterRecoveryNumerator D r hD hr a)/
        MvPolynomial.eval p.rep (parameterRecoveryDenominator D r hD a) = t := by
  obtain ⟨d,hN,hDen⟩ := parameter_recovery_homogeneous D r hr hD a
  obtain ⟨hden,hrec⟩ := parameter_rational_recovery D r hr hD a ha ha0 t ht
  obtain ⟨c,hc,heq⟩ := hp
  rw [heq,homogeneous_eval_smul _ d hN,homogeneous_eval_smul _ d hDen]
  exact ⟨mul_ne_zero (pow_ne_zero _ hc) hden,
    (mul_div_mul_left _ _ (pow_ne_zero d hc)).trans hrec⟩

#print axioms parameter_projective_rational_recovery
end NLA.TR27.Paper
