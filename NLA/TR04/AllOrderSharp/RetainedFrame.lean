module

public import NLA.TR04.AllOrderSharp.WeightedSelector

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp

def prefixInclusion (n : ℕ) : Matrix (Fin (n+1)) (Fin n) ℝ :=
  fun i j => if i = j.castSucc then 1 else 0

theorem prefixInclusion_orthonormal (n : ℕ) :
    (prefixInclusion n).transpose * prefixInclusion n = 1 := by
  classical
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.castSucc]
  · simp [prefixInclusion, Matrix.one_apply]
  · intro k _ hk
    simp [prefixInclusion, hk]
  · simp

theorem keep_prefix (n : ℕ) :
    Matrix.diagonal (keepMask (Fin.last n)) * prefixInclusion n = prefixInclusion n := by
  ext i j
  by_cases hi : i = Fin.last n
  · subst i
    simp [prefixInclusion, Matrix.diagonal_mul, keepMask]
    intro h
    have hh : n = j.val := congrArg (fun k : Fin (n+1) => k.val) h
    exact (Nat.ne_of_lt j.isLt) hh.symm
  · simp [Matrix.diagonal_mul, keepMask, hi]

theorem retained_frame_orthonormal {m n k : ℕ}
    (V : Matrix (Fin m) (Fin (n+1)) ℝ) (hV : V.transpose * V = 1)
    (U : Matrix (Fin m) (Fin k) ℝ)
    (hp : U * U.transpose * V = V * Matrix.diagonal (keepMask (Fin.last n))) :
    (U.transpose * (V * prefixInclusion n)).transpose *
      (U.transpose * (V * prefixInclusion n)) = 1 := by
  apply retained_compression_orthonormal V hV U (prefixInclusion n)
    (prefixInclusion_orthonormal n)
  calc
    _ = (U * U.transpose * V) * prefixInclusion n := by simp only [Matrix.mul_assoc]
    _ = V * prefixInclusion n := by rw [hp, Matrix.mul_assoc, keep_prefix]

theorem compressed_last_zero {m n k : ℕ}
    (V : Matrix (Fin m) (Fin (n+1)) ℝ)
    (U : Matrix (Fin m) (Fin k) ℝ) (hU : U.transpose * U = 1)
    (hp : U * U.transpose * V = V * Matrix.diagonal (keepMask (Fin.last n))) :
    ∀ i, (U.transpose * V) i (Fin.last n) = 0 := by
  have hh := congrArg (fun A => U.transpose * A) hp
  have hleft : U.transpose * (U * U.transpose * V) = U.transpose * V := by
    calc
      _ = (U.transpose * U) * (U.transpose * V) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.one_mul]
  rw [hleft] at hh
  intro i
  have he := congrArg (fun A => A i (Fin.last n)) hh
  simpa only [← Matrix.mul_assoc, Matrix.mul_diagonal, keepMask,
    if_pos rfl, ite_true, mul_zero] using he

theorem weighted_family_projection {N q m k : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (hV : V.transpose * V = 1)
    (c : Fin (q+2) → ℝ) (hpos : ∀ i, 0 < c i)
    (hanti : StrictAnti (fun i => c i ^ 2))
    (U : Matrix (Fin m) (Fin k) ℝ) (hk : k < q+2)
    (he : Reference.TensorGrouping.entryFrobeniusSq
      (family hN (V * Matrix.diagonal c) -
        U * U.transpose * family hN (V * Matrix.diagonal c)) ≤ c (Fin.last (q+1)) ^ 2) :
    U * U.transpose * V = V * Matrix.diagonal (keepMask (Fin.last (q+1))) := by
  rw [family_weighted_embedding] at he
  apply actual_projection_on_embedding V hV (family hN (Matrix.diagonal c))
    (fun i => c i ^ 2) (weighted_selector_row_gram hN c)
    (fun i => sq_pos_of_pos (hpos i)) (Fin.last (q+1)) ?_ U hk he
  intro i hi
  apply hanti
  have hh : i.val < q+1 := by
    have himax := i.isLt
    have hine : i.val ≠ q+1 := by
      intro heq
      apply hi
      exact Fin.ext heq
    omega
  exact hh

#print axioms retained_frame_orthonormal
#print axioms weighted_family_projection

end NLA.TR04.AllOrderSharp
