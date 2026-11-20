module

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-19.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
public import NLA.MI19.Definitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
namespace NLA.MI19.MovingTerms

/-- A checked decomposition enumerates permutations without an external table. -/
theorem sum_perm_succ {n : ℕ} (f : Equiv.Perm (Fin (n + 1)) → ℂ) :
    (∑ σ : Equiv.Perm (Fin (n + 1)), f σ) =
      ∑ i : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n),
        f (Equiv.Perm.decomposeFin.symm (i, τ)) := by
  rw [Finset.univ_perm_fin_succ, ← Finset.univ_product_univ]
  simp only [Finset.sum_map, Equiv.toEmbedding_apply, Finset.sum_product]

/-- The last index obtained by recursive finite-sum enumeration is index three. -/
theorem fin3_succ_two : Fin.succ (2 : Fin 3) = (3 : Fin 4) := rfl

/-- Only the six increasing pairs can contribute to inversions at order four. -/
theorem inversionCount_fin4 (σ : Equiv.Perm (Fin 4)) :
    inversionCount σ =
      (if σ 1 < σ 0 then 1 else 0) +
      (if σ 2 < σ 0 then 1 else 0) +
      (if σ 3 < σ 0 then 1 else 0) +
      (if σ 2 < σ 1 then 1 else 0) +
      (if σ 3 < σ 1 then 1 else 0) +
      (if σ 3 < σ 2 then 1 else 0) := by
  unfold inversionCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num [Fin.lt_def, -Fin.val_fin_lt, -Fin.val_pos_iff, fin3_succ_two, add_assoc]

/-- Concrete-index specializations keep the permutation reduction small. -/
theorem decomposeFin3_apply_two (p : Fin 3) (e : Equiv.Perm (Fin 2)) :
    (Equiv.Perm.decomposeFin.symm (p, e)) 2 = Equiv.swap 0 p (e 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e p 1

theorem decomposeFin4_apply_two (p : Fin 4) (e : Equiv.Perm (Fin 3)) :
    (Equiv.Perm.decomposeFin.symm (p, e)) 2 = Equiv.swap 0 p (e 1).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e p 1

theorem decomposeFin4_apply_three (p : Fin 4) (e : Equiv.Perm (Fin 3)) :
    (Equiv.Perm.decomposeFin.symm (p, e)) 3 = Equiv.swap 0 p (e 2).succ :=
  Equiv.Perm.decomposeFin_symm_apply_succ e p 2

end NLA.MI19.MovingTerms
