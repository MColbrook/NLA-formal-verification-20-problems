module

public import NLA.RA02.LiteralCauchyBinet.CauchyBinet

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace RootRA02CauchyBinet
open Finset Function Matrix
open NLA.RA02.Paper
open scoped BigOperators

theorem enumerated_exponent {n s : ℕ} (T : SizedSubset n s) :
    (∑ i : Fin s, (enumerate T i).val) = subsetExponent T := by
  classical
  unfold subsetExponent
  apply Finset.sum_bij (fun i _ => enumerate T i)
  · intro i hi
    exact T.val.orderEmbOfFin_mem T.property i
  · intro i hi j hj hij
    exact (enumerate T).injective hij
  · intro j hj
    have him : j ∈ Finset.univ.image (T.val.orderEmbOfFin T.property) := by
      simpa using hj
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp him
    exact ⟨i, hi, hij⟩
  · intro i hi
    rfl

theorem actual_paper_cauchy_binet {n s : ℕ} (rows cols : Fin s ↪ Fin n) (t : ℝ) :
    ((sharpFamily n t).submatrix rows cols).det =
      ∑ T : SizedSubset n s,
        ((lower n t).submatrix rows (enumerate T)).det *
        ((lower n t).submatrix cols (enumerate T)).det *
        epsilon n t ^ subsetExponent T := by
  classical
  let A : Matrix (Fin s) (Fin n) ℝ := fun i k => lower n t (rows i) k * epsilon n t ^ k.val
  let B : Matrix (Fin n) (Fin s) ℝ := fun k j => lower n t (cols j) k
  have hAB : (sharpFamily n t).submatrix rows cols = A * B := by
    ext i j
    change (∑ k : Fin n, (lower n t * diagonalScales n t) (rows i) k *
      lower n t (cols j) k) = _
    simp only [diagonalScales, Matrix.mul_diagonal]
    rfl
  rw [hAB, rectangular_cauchy_binet]
  apply Finset.sum_congr rfl
  intro T hT
  have hA : (A.submatrix id (enumerate T)).det =
      (∏ i : Fin s, epsilon n t ^ (enumerate T i).val) *
        ((lower n t).submatrix rows (enumerate T)).det := by
    have heq : A.submatrix id (enumerate T) = Matrix.of (fun i j : Fin s =>
        epsilon n t ^ (enumerate T j).val * lower n t (rows i) (enumerate T j)) := by
      ext i j
      change lower n t (rows i) (enumerate T j) * epsilon n t ^ (enumerate T j).val =
        epsilon n t ^ (enumerate T j).val * lower n t (rows i) (enumerate T j)
      exact mul_comm _ _
    rw [heq]
    exact Matrix.det_mul_row (fun i : Fin s => epsilon n t ^ (enumerate T i).val)
      ((lower n t).submatrix rows (enumerate T))
  have hB : (B.submatrix (enumerate T) id).det =
      ((lower n t).submatrix cols (enumerate T)).det := by
    change (((lower n t).submatrix cols (enumerate T)).transpose).det = _
    exact Matrix.det_transpose _
  rw [hA, hB, Finset.prod_pow_eq_pow_sum, enumerated_exponent]
  ring

theorem actual_ordered_paper_cauchy_binet {n s : ℕ}
    (I J : SizedSubset n s) (t : ℝ) :
    ((sharpFamily n t).submatrix (enumerate I) (enumerate J)).det =
      ∑ T : SizedSubset n s,
        ((lower n t).submatrix (enumerate I) (enumerate T)).det *
        ((lower n t).submatrix (enumerate J) (enumerate T)).det *
        epsilon n t ^ subsetExponent T :=
  actual_paper_cauchy_binet (enumerate I) (enumerate J) t

theorem actual_empty_minor (n : ℕ) (rows cols : Fin 0 ↪ Fin n) (t : ℝ) :
    ((sharpFamily n t).submatrix rows cols).det = 1 :=
  Matrix.det_isEmpty

theorem actual_full_minor_expansion (n : ℕ) (rows cols : Fin n ↪ Fin n) (t : ℝ) :
    ((sharpFamily n t).submatrix rows cols).det =
      ((lower n t).submatrix rows id).det *
      ((lower n t).submatrix cols id).det * epsilon n t ^ (n * (n - 1) / 2) := by
  classical
  have hm : (sharpFamily n t).submatrix rows cols =
      (lower n t).submatrix rows id * diagonalScales n t *
        ((lower n t).submatrix cols id).transpose := by
    ext i j
    simp [sharpFamily, diagonalScales, Matrix.submatrix_apply, Matrix.mul_apply]
  rw [hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    diagonalScales, Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ i : Fin n, i.val) = n * (n - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
  rw [hsum]
  ring

end RootRA02CauchyBinet
