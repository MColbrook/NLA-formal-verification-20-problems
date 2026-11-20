module

public import NLA.MI19.Proof
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
namespace NLA.MI19.LiteralProse

theorem full_polynomial (q : ℝ) :
    qPermanent q witness =
      115600*(q:ℂ)^6+4886140*(q:ℂ)^5+9568969*(q:ℂ)^4+4712758*(q:ℂ)^3
        -199231*(q:ℂ)^2+4886140*(q:ℂ)+4999700 := by
  unfold qPermanent
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique]
  simp only [qPermanentTerm, inversionCount_fin4, Fin.prod_univ_succ, Fin.prod_univ_zero]
  norm_num [witness, Equiv.Perm.decomposeFin_symm_apply_zero,
    Equiv.Perm.decomposeFin_symm_apply_succ, decomposeFin3_apply_two,
    decomposeFin4_apply_two, decomposeFin4_apply_three, Equiv.swap_apply_def,
    Matrix.cons_val_two, Matrix.cons_val_three, Fin.ext_iff, Fin.lt_def,
    -Fin.val_fin_lt, -Fin.val_pos_iff, -Fin.val_eq_zero_iff]
  ring

theorem restricted_polynomial (q : ℝ) :
    restrictedQPermanent q witness witnessSubset =
      4999700*(q:ℂ)^5+9482260*(q:ℂ)^4+4741130*(q:ℂ)^3+4741130*(q:ℂ)+4999700 := by
  unfold restrictedQPermanent
  rw [Finset.sum_filter]
  simp only [sum_perm_succ, Fin.sum_univ_succ, Fintype.sum_unique]
  norm_num [PreservesSubset, witnessSubset, Equiv.Perm.decomposeFin_symm_apply_zero,
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

theorem factored_difference (q : ℝ) :
    qPermanent q witness-restrictedQPermanent q witness witnessSubset =
      (q:ℂ)*((q:ℂ)+1)*(115600*(q:ℂ)^4-229160*(q:ℂ)^3+315869*(q:ℂ)^2
        -344241*(q:ℂ)+145010) := by
  rw [full_polynomial,restricted_polynomial]
  ring

#print axioms full_polynomial
#print axioms restricted_polynomial
#print axioms factored_difference
end NLA.MI19.LiteralProse
