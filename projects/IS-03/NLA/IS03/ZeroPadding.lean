module

public import NLA.IS03.Newton

@[expose] public section

/-!
The manuscript's zero-padding extension: adjoining any number of zero roots
does not change a positive power sum. These are spectral-list lemmas. The
bridge from an arbitrary realizing matrix to its root power sums is a
separate remaining obligation; no diagonalizability assumption is made here.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.IS03

theorem zero_padding_power_sum {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (r k : ℕ) (hk : k ≠ 0) :
    (∑ j : ι ⊕ Fin r, (Sum.elim μ (fun _ => (0 : ℂ)) j) ^ k) =
      ∑ i, μ i ^ k := by
  simp [Fintype.sum_sum_type, hk]

theorem zero_padding_characteristic_product {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (r : ℕ)
    (hprod : (∏ i, (X - C (μ i))) =
      derivativePolynomial.map (algebraMap ℝ ℂ)) :
    (∏ j : ι ⊕ Fin r, (X - C (Sum.elim μ (fun _ => (0 : ℂ)) j))) =
      X ^ r * derivativePolynomial.map (algebraMap ℝ ℂ) := by
  simp [Fintype.prod_sum_type, hprod, mul_comm]

theorem zero_padding_seventh_moment {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (hcard : Fintype.card ι = 6)
    (hprod : (∏ i, (X - C (μ i))) =
      derivativePolynomial.map (algebraMap ℝ ℂ)) (r : ℕ) :
    (∑ j : ι ⊕ Fin r, (Sum.elim μ (fun _ => (0 : ℂ)) j) ^ 7) =
      (-8593 / 823543 : ℂ) := by
  rw [zero_padding_power_sum μ r 7 (by decide)]
  have h := power_sums_of_derivative_product μ hcard hprod (6 : Fin 7)
  change (∑ i, μ i ^ 7) = ((-8593 / 823543 : ℝ) : ℂ) at h
  simpa using h

theorem zero_padding_negative_moment {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (hcard : Fintype.card ι = 6)
    (hprod : (∏ i, (X - C (μ i))) =
      derivativePolynomial.map (algebraMap ℝ ℂ)) (r : ℕ) :
    (∑ j : ι ⊕ Fin r, (Sum.elim μ (fun _ => (0 : ℂ)) j) ^ 7).re < 0 := by
  rw [zero_padding_seventh_moment μ hcard hprod r]
  norm_num

#print axioms zero_padding_power_sum
#print axioms zero_padding_characteristic_product
#print axioms zero_padding_seventh_moment
#print axioms zero_padding_negative_moment

end NLA.IS03
