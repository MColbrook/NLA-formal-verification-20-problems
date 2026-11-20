module

public import NLA.RA09.Spectral
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace NLA.RA09.Paper

theorem rank_eq_nonzero_eigenvalue_count {n : ℕ} {B : RealMatrix n}
    (d : OrderedSpectralData B) :
    B.rank = Fintype.card {i : Fin n // d.eigenvalues i ≠ 0} := by
  let U : RealMatrix n := d.orthogonal
  let D := Matrix.diagonal d.eigenvalues
  have hB : B = U*D*U.transpose := d.reconstruct
  have hD : U.transpose*B*U = D := by
    calc
      _ = (U.transpose*U)*D*(U.transpose*U) := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = D := by rw [orthogonal_transpose_mul d.orthogonal]; simp
  have hBD : B.rank = D.rank := by
    apply le_antisymm
    · rw [hB]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    · rw [← hD]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [hBD]
  exact Matrix.rank_diagonal _

theorem eigenvalue_zero_of_rank_le {n : ℕ} {B : RealMatrix n}
    (d : OrderedSpectralData B) (k : ℕ) (hB : B.rank ≤ k)
    (i : Fin n) (hi : k ≤ i.val) : d.eigenvalues i = 0 := by
  by_contra hn
  have heig : 0 < d.eigenvalues i := lt_of_le_of_ne (d.nonnegative i) (Ne.symm hn)
  have hk : k < n := hi.trans_lt i.isLt
  let e : Fin (k+1) → {j : Fin n // d.eigenvalues j ≠ 0} := fun j =>
    ⟨⟨j.val, (Nat.lt_succ_iff.mp j.isLt).trans_lt hk⟩,
      ne_of_gt (heig.trans_le (d.decreasing (show
        (⟨j.val, (Nat.lt_succ_iff.mp j.isLt).trans_lt hk⟩ : Fin n) ≤ i from
          (Nat.lt_succ_iff.mp j.isLt).trans hi)))⟩
  have hinj : Function.Injective e := by
    intro x y h
    apply Fin.ext
    exact congrArg (fun z : {j : Fin n // d.eigenvalues j ≠ 0} => z.val.val) h
  have hcard := Fintype.card_le_of_injective e hinj
  rw [Fintype.card_fin, ← rank_eq_nonzero_eigenvalue_count d] at hcard
  omega

theorem truncation_eq_of_rank_le {n : ℕ} {B : RealMatrix n}
    (d : OrderedSpectralData B) (k : ℕ) (hk : k ≤ n) (hB : B.rank ≤ k) :
    truncation d k = B := by
  apply (truncation_semantics_proved d k hk (fun x => x)).2.2.2.2.mpr
  exact eigenvalue_zero_of_rank_le d k hB

#print axioms rank_eq_nonzero_eigenvalue_count
#print axioms eigenvalue_zero_of_rank_le
#print axioms truncation_eq_of_rank_le

end NLA.RA09.Paper
