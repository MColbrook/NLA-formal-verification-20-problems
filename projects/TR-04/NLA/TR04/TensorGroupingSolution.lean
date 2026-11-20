module

public import NLA.TR04.TensorGrouping
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.TensorGrouping
open Reference.RealSVDPackage
open scoped BigOperators Matrix Kronecker

theorem verified_grouped_mul {ι κ : Type*} [Fintype ι] [DecidableEq ι] {m k : ℕ} (U : Rect m k) (C : Matrix (Fin k) (ι × κ) ℝ) :
    grouped (U * C) = (U ⊗ₖ (1 : Matrix ι ι ℝ)) * grouped C := by
  exact grouped_mul U C

theorem verified_grouped_compression {ι κ : Type*} [Fintype ι] [DecidableEq ι] {m k : ℕ} (U : Rect m k)
    (A : Matrix (Fin m) (ι × κ) ℝ) :
    grouped (U.transpose * A) =
      (U.transpose ⊗ₖ (1 : Matrix ι ι ℝ)) * grouped A := by
  exact grouped_compression U A

theorem verified_grouped_compression_rank_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] {m k : ℕ} (U : Rect m k)
    (A : Matrix (Fin m) (ι × κ) ℝ) :
    (grouped (U.transpose * A)).rank ≤ (grouped A).rank := by
  exact grouped_compression_rank_le U A

theorem verified_grouped_lifting_rank_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] {m k : ℕ} (U : Rect m k)
    (C : Matrix (Fin k) (ι × κ) ℝ) :
    (grouped (U * C)).rank ≤ (grouped C).rank := by
  exact grouped_lifting_rank_le U C

theorem verified_grouped_lifting_rank_eq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] {m k : ℕ} (U : Rect m k)
    (hU : U.transpose * U = 1) (C : Matrix (Fin k) (ι × κ) ℝ) :
    (grouped (U * C)).rank = (grouped C).rank := by
  exact grouped_lifting_rank_eq U hU C

theorem verified_grouped_frobeniusSq {ι κ : Type*} [Fintype ι] [Fintype κ] {m : ℕ} (A : Matrix (Fin m) (ι × κ) ℝ) :
    entryFrobeniusSq (grouped A) = entryFrobeniusSq A := by
  exact grouped_frobeniusSq A

theorem verified_grouped_compression_frobenius_le {ι κ : Type*} [Fintype ι] [Fintype κ] {m k : ℕ} (U : Rect m k)
    (hU : U.transpose * U = 1) (A : Matrix (Fin m) (ι × κ) ℝ) :
    entryFrobeniusSq (grouped (U.transpose * A)) ≤ entryFrobeniusSq (grouped A) := by
  exact grouped_compression_frobenius_le U hU A

theorem verified_grouped_lifting_frobenius_eq {ι κ : Type*} [Fintype ι] [Fintype κ] {m k : ℕ} (U : Rect m k)
    (hU : U.transpose * U = 1) (C : Matrix (Fin k) (ι × κ) ℝ) :
    entryFrobeniusSq (grouped (U * C)) = entryFrobeniusSq (grouped C) := by
  exact grouped_lifting_frobenius_eq U hU C

#print axioms Reference.TensorGrouping.verified_grouped_mul
#print axioms Reference.TensorGrouping.verified_grouped_compression
#print axioms Reference.TensorGrouping.verified_grouped_compression_rank_le
#print axioms Reference.TensorGrouping.verified_grouped_lifting_rank_le
#print axioms Reference.TensorGrouping.verified_grouped_lifting_rank_eq
#print axioms Reference.TensorGrouping.verified_grouped_frobeniusSq
#print axioms Reference.TensorGrouping.verified_grouped_compression_frobenius_le
#print axioms Reference.TensorGrouping.verified_grouped_lifting_frobenius_eq
end Reference.TensorGrouping
