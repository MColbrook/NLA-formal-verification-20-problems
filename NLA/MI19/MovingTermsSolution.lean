module

public import NLA.MI19.MovingTermsDefinitions
public import NLA.MI19.MovingTermsEnumeration

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
namespace NLA.MI19.MovingTerms

theorem integerWitness_cast (i j : Fin 4) :
    (integerWitness i j : ℂ) = witness i j := by
  fin_cases i <;> fin_cases j <;> norm_num [integerWitness, witness]

theorem moving_permutations_card :
    ((Finset.univ : Finset (Equiv.Perm (Fin 4))).filter
      (fun σ => σ 1 ≠ 1)).card = 18 := by
  decide

theorem difference_is_moving_sum (q : ℝ) :
    qPermanent q witness - restrictedQPermanent q witness witnessSubset =
      ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))).filter
        (fun σ => σ 1 ≠ 1), qPermanentTerm q witness σ := by
  have hp (σ : Equiv.Perm (Fin 4)) :
      PreservesSubset σ witnessSubset ↔ σ 1 = 1 := by
    simp [PreservesSubset, witnessSubset]
  unfold qPermanent restrictedQPermanent
  simp only [hp]
  have h := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset (Equiv.Perm (Fin 4))))
    (p := fun σ => σ 1 = 1) (f := fun σ => qPermanentTerm q witness σ)
  linear_combination -h

theorem moving_sum_factored (q : ℝ) :
    (∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin 4))).filter
      (fun σ => σ 1 ≠ 1), qPermanentTerm q witness σ) =
      (q:ℂ)*((q:ℂ)+1)*(115600*(q:ℂ)^4-229160*(q:ℂ)^3+315869*(q:ℂ)^2
        -344241*(q:ℂ)+145010) := by
  rw [Finset.sum_filter]
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique]
  norm_num [Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, decomposeFin3_apply_two,
    decomposeFin4_apply_two, decomposeFin4_apply_three, Equiv.swap_apply_def,
    Fin.ext_iff, -Fin.val_eq_zero_iff]
  simp only [qPermanentTerm, inversionCount_fin4, Fin.prod_univ_succ, Fin.prod_univ_zero]
  norm_num [witness, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, decomposeFin3_apply_two,
    decomposeFin4_apply_two, decomposeFin4_apply_three, Equiv.swap_apply_def,
    Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff, Fin.lt_def,
    -Fin.val_fin_lt, -Fin.val_pos_iff, -Fin.val_eq_zero_iff]
  ring

theorem negative_products_exactly_one_negative_entry (σ : Equiv.Perm (Fin 4)) :
    (∏ i : Fin 4, witness i (σ i)).re < 0 ↔
      ((σ 1 = 2 ∧ σ 2 ≠ 1) ∨ (σ 1 ≠ 2 ∧ σ 2 = 1)) := by
  have hfinite : ∀ τ : Equiv.Perm (Fin 4),
      (∏ i : Fin 4, integerWitness i (τ i)) < 0 ↔
        ((τ 1 = 2 ∧ τ 2 ≠ 1) ∨ (τ 1 ≠ 2 ∧ τ 2 = 1)) := by decide
  have hc : (∏ i : Fin 4, witness i (σ i)).re =
      ((∏ i : Fin 4, integerWitness i (σ i) : ℤ) : ℝ) := by
    simp only [← integerWitness_cast, ← Int.cast_prod, Complex.intCast_re]
  rw [hc]
  exact_mod_cast hfinite σ

theorem negative_terms_exactly_one_negative_entry {q : ℝ} (hq : 0 < q)
    (σ : Equiv.Perm (Fin 4)) :
    (qPermanentTerm q witness σ).re < 0 ↔
      ((σ 1 = 2 ∧ σ 2 ≠ 1) ∨ (σ 1 ≠ 2 ∧ σ 2 = 1)) := by
  simp only [qPermanentTerm, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hp : 0 < q ^ inversionCount σ := pow_pos hq _
  constructor
  · intro h
    apply (negative_products_exactly_one_negative_entry σ).mp
    by_contra hn
    have hn' : 0 ≤ (∏ i : Fin 4, witness i (σ i)).re := le_of_not_gt hn
    have hz := mul_nonneg hp.le hn'
    linarith
  · intro h
    exact mul_neg_of_pos_of_neg hp ((negative_products_exactly_one_negative_entry σ).mpr h)

#print axioms moving_permutations_card
#print axioms difference_is_moving_sum
#print axioms moving_sum_factored
#print axioms negative_products_exactly_one_negative_entry
#print axioms negative_terms_exactly_one_negative_entry
end NLA.MI19.MovingTerms
