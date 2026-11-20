module

public import NLA.TR27.PaperTangent
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Nonsingular

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Polynomial
namespace NLA.TR27.Paper

/-- Finite Vandermonde columns remain independent in every sufficiently large degree. -/
theorem finite_curve_independent {D k : ℕ} (hk : k ≤ D+1)
    (a : Fin k → ℂ) (ha : Function.Injective a) :
    LinearIndependent ℂ (fun i => curveVector D (some (a i))) := by
  have hli := Matrix.linearIndependent_rows_of_det_ne_zero
    (Matrix.det_vandermonde_ne_zero_iff.mpr ha)
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro b hb
  apply hli b
  ext j
  have h := congrFun hb (⟨j.val, lt_of_lt_of_le j.isLt hk⟩ : Fin (D+1))
  simpa [curveVector, Matrix.vandermonde, Finset.sum_apply] using h

theorem tangent_not_span_zero_and_finite (r : ℕ) (a : Fin r → ℂ) :
    tangentVector (r+1) ∉ Submodule.span ℂ
      (Set.range (fun i => curveVector (r+1) (some ((Fin.cons 0 a : Fin (r+1) → ℂ) i)))) := by
  intro h
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp h
  let f := tangentPolynomial (fun i => some (a i))
  have heval (i : Fin (r+1)) :
      coefficientPairing (r+1) f (curveVector (r+1) (some ((Fin.cons 0 a : Fin (r+1) → ℂ) i))) = 0 := by
    rw [coefficientPairing_finite _ _ (tangentPolynomial_degree _) _]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [tangentPolynomial]
    · exact tangentPolynomial_eval (fun j => some (a j)) j (a j) rfl
  have hp := congrArg (coefficientPairing (r+1) f) hb
  simp only [map_sum, map_smul, heval, smul_zero, Finset.sum_const_zero,
    coefficientPairing_tangent (r+1) (by omega)] at hp
  exact tangentPolynomial_coeff_one _ hp.symm

/-- Confluent columns, ordered u'(0), u(0), u(a_1),...,u(a_r).
This swaps the first two columns of the paper's B and has the same invertibility. -/
def confluentColumns (r : ℕ) (a : Fin r → ℂ) : Fin (r+2) → CurveSpace (r+1) :=
  Fin.cons (tangentVector (r+1))
    (fun i => curveVector (r+1) (some ((Fin.cons 0 a : Fin (r+1) → ℂ) i)))

theorem confluent_independent (r : ℕ) (a : Fin r → ℂ)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) :
    LinearIndependent ℂ (confluentColumns r a) := by
  have ht : Function.Injective (Fin.cons 0 a : Fin (r+1) → ℂ) := by
    apply Fin.cons_injective_of_injective _ ha
    rintro ⟨i, hi⟩
    exact ha0 i hi
  exact (finite_curve_independent (D := r+1) (by omega) _ ht).finCons
    (tangent_not_span_zero_and_finite r a)

def confluentMatrix (r : ℕ) (a : Fin r → ℂ) : Matrix (Fin (r+2)) (Fin (r+2)) ℂ :=
  fun i j => confluentColumns r a j i

theorem confluent_det_ne_zero (r : ℕ) (a : Fin r → ℂ)
    (ha : Function.Injective a) (ha0 : ∀ i, a i ≠ 0) :
    (confluentMatrix r a).det ≠ 0 := by
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_col
  exact confluent_independent r a ha ha0

#print axioms confluent_det_ne_zero
#print axioms confluent_independent
end NLA.TR27.Paper
