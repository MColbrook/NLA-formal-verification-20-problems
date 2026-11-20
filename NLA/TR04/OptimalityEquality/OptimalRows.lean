module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual real best-rank equality analysis through the genuine competitor kernel,
checked RA02 variational bounds and MI-13 real Gram basis. CETW25/Gilles--Wilber
attribution retained. New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.OptimalityEquality.ActualBasis
public import NLA.TR04.OptimalityEquality.WeightedEquality

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage Reference.RealColumnCompression
open scoped BigOperators Matrix

theorem frobeniusSq_eq_zero_iff {m n : ℕ} (E : Rect m n) :
    frobeniusSq E = 0 ↔ E = 0 := by
  constructor
  · intro hz
    ext i j
    have h1 : E i j ^ 2 ≤ ∑ b, E i b ^ 2 :=
      Finset.single_le_sum (fun b _ => sq_nonneg _) (Finset.mem_univ j)
    have h2 : (∑ b, E i b ^ 2) ≤ frobeniusSq E :=
      Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))
        (Finset.mem_univ i)
    have hs : E i j ^ 2 = 0 := le_antisymm (by simpa [hz] using h1.trans h2) (sq_nonneg _)
    change E i j = 0
    nlinarith
  · rintro rfl
    simp [frobeniusSq]

theorem actual_optimal_residual_gram_row_zero {m n : ℕ} (A B : Rect m n)
    (r : ℕ) (hB : B.rank ≤ r) (hopt : frobeniusSq (A-B) = singularTailSq A r)
    (c : ℝ) (hc : 0 ≤ c)
    (hbelow : ∀ i : Fin m, r ≤ i.val → singularValue A.transpose i.val ^ 2 ≤ c)
    (habove : ∀ i : Fin m, i.val < r → c ≤ singularValue A.transpose i.val ^ 2) :
    ∀ i : Fin m, c < singularValue A.transpose i.val ^ 2 →
      ∀ j : Fin n, ((leftVectorMatrix A).transpose * (A-B)) i j = 0 := by
  classical
  let E := A-B
  obtain ⟨q, U, hdim, hU, hBU⟩ := exists_kernel_frame B.transpose r
    (by rw [Matrix.rank_transpose]; exact hB)
  have hEU : E.transpose * U = A.transpose * U := by
    dsimp [E]
    rw [Matrix.transpose_sub, Matrix.sub_mul, hBU, sub_zero]
  have he : U.transpose * (A * A.transpose) * U =
      U.transpose * (E * E.transpose) * U := by
    calc
      _ = (A.transpose * U).transpose * (A.transpose * U) := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = (E.transpose * U).transpose * (E.transpose * U) := by rw [hEU]
      _ = _ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hlo : singularTailSq A.transpose r ≤
      (U.transpose * (E * E.transpose) * U).trace := by
    have h := singularTail_le_compression_trace A.transpose r hdim U hU
    simp only [Matrix.transpose_transpose] at h
    rw [he] at h
    exact h
  have hhi : (U.transpose * (E * E.transpose) * U).trace ≤ frobeniusSq E.transpose := by
    simpa only [Matrix.transpose_transpose] using frobenius_compression_bound E.transpose U hU
  have htop : frobeniusSq E.transpose = singularTailSq A.transpose r := by
    simpa only [frobeniusSq_transpose, singularTailSq_transpose, E] using hopt
  rw [htop] at hhi
  have htrace : (U.transpose * (E * E.transpose) * U).trace = singularTailSq A.transpose r :=
    le_antisymm hhi hlo
  have hnorm : frobeniusSq (U.transpose * E) =
      (U.transpose * (E * E.transpose) * U).trace := by
    rw [← frobeniusSq_transpose (U.transpose * E), Matrix.transpose_mul,
      Matrix.transpose_transpose, frobeniusSq_eq_gram_trace]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hnormeq : frobeniusSq (U.transpose * E) = frobeniusSq E := by
    rw [hnorm, htrace, singularTailSq_transpose]
    exact hopt.symm
  have hd := orthonormal_column_error_decomposition U hU E (0 : Rect q n)
  simp only [Matrix.mul_zero, sub_zero, hnormeq] at hd
  have hz : E - U * U.transpose * E = 0 :=
    (frobeniusSq_eq_zero_iff (E - U * U.transpose * E)).mp (by linarith [hd])
  have hRange : E = U * U.transpose * E := sub_eq_zero.mp hz
  let V := leftVectorMatrix A
  let W : Rect m q := V.transpose * U
  have hV : IsOrthogonal V := leftVectorMatrix_orthogonal A
  have hW : W.transpose * W = 1 := by
    dsimp [W]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = U.transpose * (V * V.transpose) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV.2, Matrix.mul_one, hU]
  have hw := frame_weights_bounds W hW
  have hdiag : V.transpose * (A * A.transpose) * V =
      Matrix.diagonal (fun i : Fin m => singularValue A.transpose i.val ^ 2) :=
    leftVectorMatrix_gram_diagonal A
  have hmat : U.transpose * (A * A.transpose) * U =
      W.transpose * Matrix.diagonal (fun i : Fin m => singularValue A.transpose i.val ^ 2) * W := by
    rw [← hdiag]
    dsimp [W]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    symm
    calc
      _ = U.transpose * (V * V.transpose) * (A * A.transpose) *
          (V * V.transpose) * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV.2]; simp
  have hspec : (U.transpose * (A * A.transpose) * U).trace =
      ∑ i, singularValue A.transpose i.val ^ 2 * ∑ j, W i j ^ 2 := by
    rw [hmat, frame_diagonal_compression_trace]
  have hsum : (∑ i, singularValue A.transpose i.val ^ 2 * ∑ j, W i j ^ 2) =
      singularTailSq A.transpose r := by
    rw [← hspec, he, htrace]
  have hweights := weighted_tail_equality_zero_above
    (Finset.univ.filter (fun i : Fin m => r ≤ i.val))
    (fun i : Fin m => singularValue A.transpose i.val ^ 2)
    (fun i => ∑ j, W i j ^ 2) c hc hw.1
    (fun i hi => hbelow i (Finset.mem_filter.mp hi).2)
    (fun i hi => habove i (by simpa using hi))
    (by rw [tail_index_card, hw.2]; exact_mod_cast hdim)
    (by simpa only [singularTailSq] using hsum)
  intro i hi j
  have hzero := hweights i hi
  have hrow : ∀ l : Fin q, W i l = 0 := by
    intro l
    have hb : W i l ^ 2 ≤ ∑ t, W i t ^ 2 :=
      Finset.single_le_sum (fun t _ => sq_nonneg _) (Finset.mem_univ l)
    rw [hzero] at hb
    nlinarith
  change (V.transpose * E) i j = 0
  rw [hRange]
  have hprod : V.transpose * (U * U.transpose * E) = W * (U.transpose * E) := by
    simp only [W, Matrix.mul_assoc]
  rw [hprod]
  simp only [Matrix.mul_apply, hrow, zero_mul, Finset.sum_const_zero]

#print axioms actual_optimal_residual_gram_row_zero
end
end Reference.RealOptimalityEquality
