module

public import NLA.TR27.ArbitraryHomogeneous
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

theorem eval_parameterSubstitution (D r : ℕ) (a : Fin r → ℂ) (u : Fin 2 → ℂ)
    (p : ImageCoordinatePolynomial D) :
    MvPolynomial.eval u (parameterSubstitution D r a p) =
      MvPolynomial.eval (parameterHomogeneousMap D r a u) p := by
  exact MvPolynomial.comp_aeval_apply (parameterHomogeneousCoordinate D r a)
    (MvPolynomial.aeval u) p

private theorem integral_relation_monic {R : Type*} [CommRing R] [Nontrivial R] [Algebra ℂ R]
    (f g : R) (b c : ℂ) (r j : ℕ) (hj : 2 ≤ j)
    (hL : (-b)^j+(r : ℂ)^(j-1)*c ≠ 0) :
    (Polynomial.C (algebraMap ℂ R (((-b)^j+(r : ℂ)^(j-1)*c)⁻¹)) *
      ((Polynomial.C f - Polynomial.C (algebraMap ℂ R b)*Polynomial.X)^j -
        Polynomial.C (algebraMap ℂ R ((r : ℂ)^(j-1))) * Polynomial.X^(j-1) *
          (Polynomial.C g - Polynomial.C (algebraMap ℂ R c)*Polynomial.X))).Monic := by
  let P : Polynomial R := Polynomial.C f - Polynomial.C (algebraMap ℂ R b)*Polynomial.X
  let Q : Polynomial R := Polynomial.C g - Polynomial.C (algebraMap ℂ R c)*Polynomial.X
  have hP : P.natDegree ≤ 1 := by dsimp [P]; compute_degree
  have hQ : Q.natDegree ≤ 1 := by dsimp [Q]; compute_degree
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one j
  · apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · simpa [P] using Polynomial.natDegree_pow_le_of_le j hP
    · apply Polynomial.natDegree_mul_le.trans
      have hp := Polynomial.natDegree_C_mul_le
        (algebraMap ℂ R ((r : ℂ)^(j-1))) (Polynomial.X^(j-1) : Polynomial R)
      have hx : (Polynomial.X^(j-1) : Polynomial R).natDegree ≤ j-1 := by compute_degree
      change _+Q.natDegree ≤ j
      omega
  · have hp := Polynomial.coeff_pow_of_natDegree_le (m := j) hP
    have hdiff : j-(j-1) = 1 := by omega
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_sub]
    rw [show (Polynomial.C f-Polynomial.C (algebraMap ℂ R b)*Polynomial.X)^j = P^j by rfl]
    rw [show (P^j).coeff j = (P.coeff 1)^j by simpa using hp]
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    simp only [show j-1 ≤ j by omega, if_true, hdiff]
    simp only [P, Q, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
      Polynomial.coeff_C, Polynomial.coeff_X, one_ne_zero, if_false, if_true,
      mul_one, zero_sub]
    rw [← map_neg, ← map_pow, ← map_neg, ← map_mul, ← map_sub, ← map_mul]
    have he : ((-b)^j+(r : ℂ)^(j-1)*c)⁻¹ *
        ((-b)^j-(r : ℂ)^(j-1)*(-c)) = 1 := by
      rw [mul_neg, sub_neg_eq_add, inv_mul_cancel₀ hL]
    rw [he, map_one]

variable (D r : ℕ) (a : Fin r → ℂ)

abbrev parameterAlgebra : Algebra (ImageCoordinatePolynomial D) CurveParameterPolynomial :=
  (parameterSubstitution D r a : ImageCoordinatePolynomial D →+* CurveParameterPolynomial).toAlgebra

theorem parameter_algebraMap :
    letI := parameterAlgebra D r a
    algebraMap (ImageCoordinatePolynomial D) CurveParameterPolynomial =
      (parameterSubstitution D r a : ImageCoordinatePolynomial D →+* CurveParameterPolynomial) := rfl

theorem parameter_integral_constant (c : ℂ) :
    letI := parameterAlgebra D r a
    IsIntegral (ImageCoordinatePolynomial D) (MvPolynomial.C c : CurveParameterPolynomial) := by
  letI := parameterAlgebra D r a
  simpa [parameter_algebraMap, parameterSubstitution] using
    (isIntegral_algebraMap (R := ImageCoordinatePolynomial D) (A := CurveParameterPolynomial)
      (x := MvPolynomial.C c))

theorem parameter_integral_coordinate (j : Fin D) :
    letI := parameterAlgebra D r a
    IsIntegral (ImageCoordinatePolynomial D) (parameterHomogeneousCoordinate D r a j) := by
  letI := parameterAlgebra D r a
  simpa [parameter_algebraMap, parameterSubstitution] using
    (isIntegral_algebraMap (R := ImageCoordinatePolynomial D) (A := CurveParameterPolynomial)
      (x := MvPolynomial.X j))

theorem parameter_zero_power_integral (hD : 1 ≤ D) (hr : 1 ≤ r) (hgap : 1+r < D) :
    letI := parameterAlgebra D r a
    IsIntegral (ImageCoordinatePolynomial D)
      ((MvPolynomial.X (0 : Fin 2) : CurveParameterPolynomial)^D) := by
  letI := parameterAlgebra D r a
  obtain ⟨j,hj,hL⟩ := parameter_integral_moment D r hD hr hgap a
  let z := projectionCenter D r (fun i => some (a i))
  let n := j.succ.val
  let b : ℂ := z ⟨1,by omega⟩
  let c : ℂ := z j.succ
  let L : ℂ := (-b)^n+(r : ℂ)^(n-1)*c
  let f : ImageCoordinatePolynomial D := MvPolynomial.X ⟨0,by omega⟩
  let g : ImageCoordinatePolynomial D := MvPolynomial.X j
  let P : Polynomial (ImageCoordinatePolynomial D) :=
    Polynomial.C (MvPolynomial.C L⁻¹) *
      ((Polynomial.C f-Polynomial.C (MvPolynomial.C b)*Polynomial.X)^n -
        Polynomial.C (MvPolynomial.C ((r : ℂ)^(n-1)))*Polynomial.X^(n-1)*
          (Polynomial.C g-Polynomial.C (MvPolynomial.C c)*Polynomial.X))
  refine ⟨P, integral_relation_monic f g b c r n hj hL, ?_⟩
  simp only [P, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X]
  rw [parameter_algebraMap]
  apply MvPolynomial.funext
  intro u
  simp only [map_mul,map_sub,map_pow,map_zero,MvPolynomial.eval_X]
  change MvPolynomial.eval u (parameterSubstitution D r a (MvPolynomial.C L⁻¹)) *
      ((MvPolynomial.eval u (parameterSubstitution D r a f) -
          MvPolynomial.eval u (parameterSubstitution D r a (MvPolynomial.C b))*u 0^D)^n -
        (MvPolynomial.eval u (parameterSubstitution D r a (MvPolynomial.C (r : ℂ))))^(n-1) *
          (u 0^D)^(n-1) *
          (MvPolynomial.eval u (parameterSubstitution D r a g) -
            MvPolynomial.eval u (parameterSubstitution D r a (MvPolynomial.C c))*u 0^D)) = 0
  simp only [eval_parameterSubstitution]
  simp only [f,g,MvPolynomial.eval_C,MvPolynomial.eval_X]
  rw [parameterHomogeneousMap_apply,parameterHomogeneousMap_apply]
  simp only [Fin.val_succ,Nat.zero_add,pow_one]
  change L⁻¹ * (((r : ℂ)*u 0^(D-1)*u 1+b*u 0^D-b*u 0^D)^n-
    (r : ℂ)^(n-1)*(u 0^D)^(n-1)*
      ((r : ℂ)*u 0^(D-n)*u 1^n+c*u 0^D-c*u 0^D)) = 0
  have hn : n ≤ D := by dsimp [n]; omega
  have he : (D-1)*n = D*(n-1)+(D-n) := by
    have hD1 : D-1+1 = D := by omega
    have hn1 : n-1+1 = n := by omega
    have hDn : D-n+n = D := by omega
    nlinarith
  have hn1 : n-1+1 = n := by omega
  simp only [add_sub_cancel_right]
  rw [mul_pow,mul_pow,← pow_mul,← pow_mul]
  have hpr : (r : ℂ)^(n-1)*(r : ℂ) = (r : ℂ)^n := by
    rw [← pow_succ,hn1]
  have hps : u 0^(D*(n-1))*u 0^(D-n) = u 0^((D-1)*n) := by
    rw [← pow_add,← he]
  rw [← hpr,← hps]
  ring

theorem parameter_one_power_integral (hD : 1 ≤ D) (hr : 1 ≤ r) (hgap : 1+r < D) :
    letI := parameterAlgebra D r a
    IsIntegral (ImageCoordinatePolynomial D)
      ((MvPolynomial.X (1 : Fin 2) : CurveParameterPolynomial)^D) := by
  letI := parameterAlgebra D r a
  let j : Fin D := ⟨D-1,by omega⟩
  have h := (parameter_integral_constant D r a ((r : ℂ)⁻¹)).mul
    ((parameter_integral_coordinate D r a j).sub
      ((parameter_integral_constant D r a
        (projectionCenter D r (fun i => some (a i)) j.succ)).mul
          (parameter_zero_power_integral D r a hD hr hgap)))
  convert h using 1 <;> try rfl
  apply MvPolynomial.funext
  intro u
  simp only [map_mul, map_sub, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]
  change u 1^D = (r : ℂ)⁻¹ * (parameterHomogeneousMap D r a u j -
    projectionCenter D r (fun i => some (a i)) j.succ*u 0^D)
  rw [parameterHomogeneousMap_apply]
  have hj : j.succ.val = D := by dsimp [j]; omega
  simp only [hj, Nat.sub_self, pow_zero, mul_one, add_sub_cancel_right]
  have hr0 : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

theorem parameter_substitution_integral (hD : 1 ≤ D) (hr : 1 ≤ r) (hgap : 1+r < D) :
    (parameterSubstitution D r a : ImageCoordinatePolynomial D →+* CurveParameterPolynomial).IsIntegral := by
  letI := parameterAlgebra D r a
  have hvar (j : Fin 2) : IsIntegral (ImageCoordinatePolynomial D)
      (MvPolynomial.X j : CurveParameterPolynomial) := by
    fin_cases j
    · exact IsIntegral.of_pow (by omega : 0 < D) (parameter_zero_power_integral D r a hD hr hgap)
    · exact IsIntegral.of_pow (by omega : 0 < D) (parameter_one_power_integral D r a hD hr hgap)
  intro p
  change IsIntegral (ImageCoordinatePolynomial D) p
  induction p using MvPolynomial.induction_on with
  | C c => exact parameter_integral_constant D r a c
  | add p q hp hq => exact hp.add hq
  | mul_X p j hp => exact hp.mul (hvar j)

theorem parameter_zeroLocus_eq_range (hD : 1 ≤ D) (hr : 1 ≤ r) (hgap : 1+r < D) :
    MvPolynomial.zeroLocus ℂ (parameterImageIdeal D r a) =
      Set.range (parameterHomogeneousMap D r a) := by
  letI := parameterAlgebra D r a
  let : Algebra.IsIntegral (ImageCoordinatePolynomial D) CurveParameterPolynomial :=
    ⟨parameter_substitution_integral D r a hD hr hgap⟩
  apply Set.Subset.antisymm
  · intro w hw
    let M : Ideal (ImageCoordinatePolynomial D) := MvPolynomial.vanishingIdeal ℂ {w}
    have hM : M.IsMaximal := inferInstance
    have hker : RingHom.ker (algebraMap (ImageCoordinatePolynomial D) CurveParameterPolynomial) ≤ M := by
      intro p hp
      change p ∈ parameterImageIdeal D r a at hp
      simpa only [M,MvPolynomial.mem_vanishingIdeal_iff,Set.mem_singleton_iff,forall_eq] using hw p hp
    obtain ⟨N,hN,hcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral M hker
    obtain ⟨u,hu⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hN
    refine ⟨u, ?_⟩
    funext j
    have hj : MvPolynomial.X j-MvPolynomial.C (w j) ∈ M := by simp [M]
    rw [← hcomap] at hj
    change algebraMap (ImageCoordinatePolynomial D) CurveParameterPolynomial
      (MvPolynomial.X j-MvPolynomial.C (w j)) ∈ N at hj
    rw [hu] at hj
    have heval := (MvPolynomial.mem_vanishingIdeal_iff.mp hj) u (Set.mem_singleton u)
    change MvPolynomial.eval u (parameterSubstitution D r a
      (MvPolynomial.X j-MvPolynomial.C (w j))) = 0 at heval
    rw [eval_parameterSubstitution] at heval
    simpa only [map_sub,MvPolynomial.eval_X,MvPolynomial.eval_C,sub_eq_zero] using heval
  · rintro w ⟨u,rfl⟩
    intro p hp
    change parameterSubstitution D r a p = 0 at hp
    change MvPolynomial.eval (parameterHomogeneousMap D r a u) p = 0
    rw [← eval_parameterSubstitution,hp,map_zero]

#print axioms parameter_substitution_integral
#print axioms parameter_zeroLocus_eq_range
end NLA.TR27.Paper
