module

public import NLA.TR27.PaperCurveDefinitions
public import NLA.TR27.Independence
public import NLA.TR27.Semantics
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
open Polynomial
namespace NLA.TR27.Paper

def coefficientPairing (D : ℕ) (f : ℂ[X]) : CurveSpace D →ₗ[ℂ] ℂ :=
  ∑ j : Fin (D + 1), f.coeff (j : ℕ) • LinearMap.proj j

theorem coefficientPairing_apply (D : ℕ) (f : ℂ[X]) (v : CurveSpace D) :
    coefficientPairing D f v = ∑ j : Fin (D + 1), f.coeff (j : ℕ) * v j := by
  simp [coefficientPairing]

theorem coefficientPairing_tangent (D : ℕ) (hD : 1 ≤ D) (f : ℂ[X]) :
    coefficientPairing D f (tangentVector D) = f.coeff 1 := by
  classical
  rw [coefficientPairing_apply]
  have heq : tangentVector D = fun j : Fin (D + 1) =>
      if j = (⟨1, by omega⟩ : Fin (D + 1)) then 1 else 0 := by
    funext j
    simp [tangentVector, Fin.ext_iff]
  simp [heq, mul_ite]

theorem coefficientPairing_finite (D : ℕ) (f : ℂ[X]) (hf : f.natDegree ≤ D) (a : ℂ) :
    coefficientPairing D f (curveVector D (some a)) = f.eval a := by
  rw [coefficientPairing_apply, Polynomial.eval_eq_sum,
    Polynomial.sum_over_range' f (fun n => zero_mul (a ^ n)) (D+1) (by omega)]
  simpa [curveVector] using
    (Fin.sum_univ_eq_sum_range (fun j => f.coeff j * a ^ j) (D+1))

theorem coefficientPairing_infinity (D : ℕ) (f : ℂ[X]) :
    coefficientPairing D f (curveVector D none) = f.coeff D := by
  classical
  rw [coefficientPairing_apply]
  have heq : curveVector D none = fun j : Fin (D + 1) =>
      if j = Fin.last D then 1 else 0 := by
    funext j
    simp [curveVector, Fin.ext_iff]
  simp [heq, mul_ite]

theorem tangent_polynomial_annihilates {D k : ℕ} (hk : k < D)
    (t : Fin k → Option ℂ) (i : Fin k) :
    coefficientPairing D (tangentPolynomial t) (curveVector D (t i)) = 0 := by
  cases hti : t i with
  | none =>
      rw [coefficientPairing_infinity]
      exact Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (tangentPolynomial_degree_of_none t i hti) hk)
  | some a =>
      rw [coefficientPairing_finite _ _ (by have := tangentPolynomial_degree t; omega)]
      exact tangentPolynomial_eval t i a hti

/-- Lower bound allows repetitions, finite zero, infinity and arbitrary coefficients. -/
theorem tangent_not_short_sum {D k : ℕ} (hD : 1 ≤ D) (hk : k < D)
    (t : Fin k → Option ℂ) (a : Fin k → ℂ) :
    tangentVector D ≠ ∑ i, a i • curveVector D (t i) := by
  intro h
  have hp := congrArg (coefficientPairing D (tangentPolynomial t)) h
  simp only [coefficientPairing_tangent D hD, map_sum, map_smul,
    tangent_polynomial_annihilates hk, smul_zero, Finset.sum_const_zero] at hp
  exact tangentPolynomial_coeff_one t hp

theorem tangentVector_ne_zero (D : ℕ) (hD : 1 ≤ D) : tangentVector D ≠ 0 := by
  intro h
  have := congrFun h (⟨1, by omega⟩ : Fin (D+1))
  simpa [tangentVector] using this

theorem curveVector_ne_zero (D : ℕ) (t : Option ℂ) : curveVector D t ≠ 0 := by
  intro h
  cases t with
  | none => have := congrFun h (Fin.last D); simpa [curveVector] using this
  | some a => have := congrFun h 0; simpa [curveVector] using this

theorem tangent_projective_lower (D : ℕ) (hD : 1 ≤ D) (k : ℕ) (hk : k < D) :
    ¬ ProjectiveRankAtMost (curvePoints D) k
      (Projectivization.mk ℂ (tangentVector D) (tangentVector_ne_zero D hD)) := by
  classical
  rintro ⟨l, hl, q, hq, hspan⟩
  obtain ⟨a, ha⟩ := (projective_span_range l q _ _).mp hspan
  choose t c hc heq using hq
  apply tangent_not_short_sum hD (lt_of_le_of_lt hl hk) t (fun i => a i * c i)
  rw [ha]
  apply Finset.sum_congr rfl
  intro i _
  rw [heq i, smul_smul]

theorem root_sum_coordinate {D : ℕ} (hD : 2 ≤ D) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ D) (j : Fin (D+1)) :
    (∑ i : Fin D, (ζ ^ (D-1+j.val)) ^ (i : ℕ)) =
      if j.val = 1 then (D : ℂ) else 0 := by
  by_cases hj : j.val = 1
  · rw [if_pos hj, hj, Nat.sub_add_cancel (by omega), hζ.pow_eq_one]
    simp
  · rw [if_neg hj, Fin.sum_univ_eq_sum_range]
    have hne : ζ ^ (D-1+j.val) ≠ 1 := by
      intro he
      obtain ⟨q, hq⟩ := (hζ.pow_eq_one_iff_dvd _).mp he
      have hepos : 0 < D-1+j.val := by omega
      have heless : D-1+j.val < D*2 := by omega
      have hqpos : 0 < q := by nlinarith
      have hqlt : q < 2 := by nlinarith
      have : q = 1 := by omega
      subst q
      simp only [mul_one] at hq
      omega
    have hp : (ζ ^ (D-1+j.val)) ^ D = 1 := by
      rw [← pow_mul, Nat.mul_comm (D-1+j.val) D, pow_mul, hζ.pow_eq_one, one_pow]
    have hm := geom_sum_mul (ζ ^ (D-1+j.val)) D
    rw [hp, sub_self] at hm
    exact (mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hne)

/-- The D-term roots-of-unity decomposition of the actual tangent vector. -/
theorem tangent_root_decomposition {D : ℕ} (hD : 2 ≤ D) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ D) :
    tangentVector D = ∑ i : Fin D,
      ((D : ℂ)⁻¹ * (ζ ^ (D-1)) ^ (i : ℕ)) • curveVector D (some (ζ ^ (i : ℕ))) := by
  ext j
  simp only [tangentVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, curveVector]
  have heq (i : Fin D) :
      ((D : ℂ)⁻¹ * (ζ ^ (D-1)) ^ (i : ℕ)) * (ζ ^ (i : ℕ)) ^ (j : ℕ) =
      (D : ℂ)⁻¹ * (ζ ^ (D-1+j.val)) ^ (i : ℕ) := by
    rw [mul_assoc, ← pow_mul, ← pow_mul, ← pow_add, ← pow_mul]
    congr 2
    ring
  simp_rw [heq]
  rw [← Finset.mul_sum, root_sum_coordinate hD hζ j]
  split_ifs <;> simp [Nat.cast_ne_zero.mpr (show D ≠ 0 by omega)]

theorem tangent_projective_upper (D : ℕ) (hD : 2 ≤ D) :
    ProjectiveRankAtMost (curvePoints D) D
      (Projectivization.mk ℂ (tangentVector D) (tangentVector_ne_zero D (by omega))) := by
  classical
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / D)
  have hζ : IsPrimitiveRoot ζ D := Complex.isPrimitiveRoot_exp D (by omega)
  let q : Fin D → ℙ ℂ (CurveSpace D) := fun i =>
    Projectivization.mk ℂ (curveVector D (some (ζ ^ (i : ℕ)))) (curveVector_ne_zero D _)
  refine ⟨D, le_rfl, q, ?_, ?_⟩
  · intro i
    exact ⟨some (ζ ^ (i : ℕ)), represents_mk _ _⟩
  · rw [projective_span_mk, tangent_root_decomposition hD hζ]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    apply (projective_span_mk (Set.range q) _ (curveVector_ne_zero D _)).mp
    exact Projectivization.Subspace.subset_span (Set.range q) (Set.mem_range_self i)

/-- The paper's tangent-rank lemma for every degree D at least two. -/
theorem rational_normal_tangent_rank (D : ℕ) (hD : 2 ≤ D) :
    projectiveRank (curvePoints D)
      (Projectivization.mk ℂ (tangentVector D) (tangentVector_ne_zero D (by omega))) = D := by
  apply IsLeast.csInf_eq
  refine ⟨tangent_projective_upper D hD, ?_⟩
  intro k hk
  exact le_of_not_gt (fun hlt => tangent_projective_lower D (by omega) k hlt hk)

#print axioms rational_normal_tangent_rank
end NLA.TR27.Paper
