module

public import Mathlib.Algebra.Order.Star.Real

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Real adaptation of the accepted RA02 PaperProjectionWeights, PaperKernelFrame,
PaperKyFan and PaperFrobeniusCompression arguments. Variational step attribution:
Chen, Epperly, Tropp and Webber, CPAM 2025, Section 5.4, and Gilles--Wilber,
arXiv:2601.22344, Appendix A.1. Adapted by Codex, 2026-10-03.
Actual real Gram diagonalization is adapted from upstream OpenProblemsInNLA
MI-13, commit e375a6fc0a12df52c4f5a38b53df78b837e1c390.
-/
public import NLA.TR04.RealSVD.RealTruncation
public import NLA.TR04.RealSVD.SingularSemantics
public import NLA.TR04.RealSVD.RealWeights
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace Reference.RealSVDPackage

theorem frame_projection_idempotent {n q : ℕ} (U : Rect n q)
    (hU : U.transpose * U = 1) :
    (U * U.transpose) * (U * U.transpose) = U * U.transpose := by
  calc
    _ = U * (U.transpose * U) * U.transpose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one]

theorem frame_complement_posSemidef {n q : ℕ} (U : Rect n q)
    (hU : U.transpose * U = 1) : (1 - U * U.transpose).PosSemidef := by
  have hh : (1 - U * U.transpose).transpose * (1 - U * U.transpose) =
      1 - U * U.transpose := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      frame_projection_idempotent U hU]
    abel
  rw [← hh, ← Matrix.conjTranspose_eq_transpose_of_trivial (1 - U * U.transpose)]
  exact Matrix.posSemidef_conjTranspose_mul_self (1 - U * U.transpose)

theorem frame_diagonal_weights {n q : ℕ} (U : Rect n q) (i : Fin n) :
    (∑ j, U i j ^ 2) = (U * U.transpose) i i := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]

theorem frame_weights_bounds {n q : ℕ} (U : Rect n q)
    (hU : U.transpose * U = 1) :
    (∀ i, 0 ≤ ∑ j, U i j ^ 2 ∧ (∑ j, U i j ^ 2) ≤ 1) ∧
    (∑ i, ∑ j, U i j ^ 2) = (q : ℝ) := by
  constructor
  · intro i
    constructor
    · exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
    · have hp := (frame_complement_posSemidef U hU).diag_nonneg (i := i)
      rw [Matrix.sub_apply, Matrix.one_apply_eq, ← frame_diagonal_weights U i] at hp
      linarith
  · simp_rw [frame_diagonal_weights U]
    change (U * U.transpose).trace = (q : ℝ)
    rw [Matrix.trace_mul_comm, hU]
    simp

theorem exists_kernel_frame {m n : ℕ} (B : Rect m n) (r : ℕ) (hr : B.rank ≤ r) :
    ∃ (q : ℕ) (U : Rect n q), n-r ≤ q ∧ U.transpose * U = 1 ∧ B * U = 0 := by
  let L := Matrix.toEuclideanLin B
  let K := LinearMap.ker L
  let q := Module.finrank ℝ K
  let b := stdOrthonormalBasis ℝ K
  let U : Rect n q := fun i j => (b j : EuclideanSpace ℝ (Fin n)) i
  have hRank : B.rank = Module.finrank ℝ (LinearMap.range L) := by
    exact Matrix.rank_eq_finrank_range_toLin B
      (PiLp.basisFun 2 ℝ (Fin m)) (PiLp.basisFun 2 ℝ (Fin n))
  have hdim := LinearMap.finrank_range_add_finrank_ker L
  rw [← hRank, finrank_euclideanSpace_fin] at hdim
  refine ⟨q, U, ?_, ?_, ?_⟩
  · change n-r ≤ Module.finrank ℝ (LinearMap.ker L)
    omega
  · ext j l
    have hinner := b.inner_eq_ite j l
    have he : (U.transpose * U) j l = inner ℝ (b j) (b l) := by
      change (∑ i, (b j : EuclideanSpace ℝ (Fin n)) i *
          (b l : EuclideanSpace ℝ (Fin n)) i) =
        ∑ i, (b l : EuclideanSpace ℝ (Fin n)) i *
          star ((b j : EuclideanSpace ℝ (Fin n)) i)
      apply Finset.sum_congr rfl
      intro i _
      simp only [star_trivial]
      ring
    rw [he, hinner]
    rfl
  · ext i j
    have hj : L (b j : EuclideanSpace ℝ (Fin n)) = 0 := (b j).property
    exact congrArg (fun v : EuclideanSpace ℝ (Fin m) => v i) hj

theorem frobenius_compression_bound {m n q : ℕ} (E : Rect m n)
    (U : Rect n q) (hU : U.transpose * U = 1) :
    (U.transpose * (E.transpose * E) * U).trace ≤ frobeniusSq E := by
  have hP := (frame_complement_posSemidef U hU).mul_mul_conjTranspose_same E
  have hn := hP.trace_nonneg
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hn
  have he : (E * (1 - U * U.transpose) * E.transpose).trace =
      (E.transpose * E).trace - (U.transpose * (E.transpose * E) * U).trace := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.trace_sub]
    congr 1
    · exact Matrix.trace_mul_comm E E.transpose
    · calc
        _ = ((E * U) * (U.transpose * E.transpose)).trace := by
          simp only [Matrix.mul_assoc]
        _ = ((U.transpose * E.transpose) * (E * U)).trace :=
          Matrix.trace_mul_comm (E * U) (U.transpose * E.transpose)
        _ = _ := by simp only [Matrix.mul_assoc]
  rw [he] at hn
  rw [frobeniusSq_eq_gram_trace]
  exact sub_nonneg.mp hn

theorem frame_diagonal_compression_trace {n q : ℕ} (d : Fin n → ℝ)
    (U : Rect n q) :
    (U.transpose * Matrix.diagonal d * U).trace = ∑ i, d i * ∑ j, U i j ^ 2 := by
  rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [frame_diagonal_weights]

theorem tail_index_card (n r : ℕ) :
    (Finset.univ.filter (fun i : Fin n => r ≤ i.val)).card = n-r := by
  by_cases hr : r < n
  · have he : Finset.univ.filter (fun i : Fin n => r ≤ i.val) =
        Finset.Ici (⟨r, hr⟩ : Fin n) := by
      ext i
      simp [Fin.le_iff_val_le_val]
    rw [he, Fin.card_Ici]
  · have he : Finset.univ.filter (fun i : Fin n => r ≤ i.val) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have hri := (Finset.mem_filter.mp hi).2
      omega
    rw [he, Finset.card_empty]
    omega

theorem singularTail_le_compression_trace {m n q : ℕ} (A : Rect m n)
    (r : ℕ) (hq : n-r ≤ q) (U : Rect n q) (hU : U.transpose * U = 1) :
    singularTailSq A r ≤ (U.transpose * (A.transpose * A) * U).trace := by
  obtain ⟨V, hV, hdiag⟩ := rectangular_right_gram_diagonal A
  let W : Rect n q := V.transpose * U
  have hW : W.transpose * W = 1 := by
    dsimp [W]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = U.transpose * (V * V.transpose) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV.2, Matrix.mul_one, hU]
  have hw := frame_weights_bounds W hW
  have hs := singular_values_semantics A
  have ha : Antitone (fun i : Fin n => singularValue A i.val ^ 2) := by
    intro i j hij
    exact pow_le_pow_left₀ (hs.1 _) (hs.2.1 (Fin.le_iff_val_le_val.mp hij)) 2
  have hb := ordered_weighted_tail_bound (fun i : Fin n => singularValue A i.val ^ 2)
    (fun i => ∑ j, W i j ^ 2) r ha (fun i => sq_nonneg _) hw.1
    (by rw [tail_index_card, hw.2]; exact_mod_cast hq)
  have he : U.transpose * (A.transpose * A) * U =
      W.transpose * Matrix.diagonal (fun i : Fin n => singularValue A i.val ^ 2) * W := by
    rw [← hdiag]
    dsimp [W]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    symm
    calc
      _ = U.transpose * (V * V.transpose) * (A.transpose * A) *
          (V * V.transpose) * U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV.2]; simp
  rw [he, frame_diagonal_compression_trace]
  exact hb

theorem singularTail_le_lowRankError {m n : ℕ} (A B : Rect m n)
    (r : ℕ) (hB : B.rank ≤ r) : singularTailSq A r ≤ frobeniusSq (A-B) := by
  obtain ⟨q, U, hdim, hU, hBU⟩ := exists_kernel_frame B r hB
  have hEU : (A-B) * U = A * U := by rw [Matrix.sub_mul, hBU, sub_zero]
  have he : U.transpose * (A.transpose * A) * U =
      U.transpose * ((A-B).transpose * (A-B)) * U := by
    calc
      _ = (A * U).transpose * (A * U) := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = ((A-B) * U).transpose * ((A-B) * U) := by rw [hEU]
      _ = _ := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hb := singularTail_le_compression_trace A r hdim U hU
  rw [he] at hb
  exact hb.trans (frobenius_compression_bound (A-B) U hU)

theorem real_best_rank_frobenius_attainment {m n : ℕ} (A : Rect m n) (r : ℕ) :
    ∃ B : Rect m n, B.rank ≤ r ∧ frobeniusSq (A-B) = singularTailSq A r ∧
      ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C) := by
  obtain ⟨B, hB, he⟩ := real_rank_r_frobenius_attainment A r
  refine ⟨B, hB, he, ?_⟩
  intro C hC
  rw [he]
  exact singularTail_le_lowRankError A C r hC

#print axioms exists_kernel_frame
#print axioms singularTail_le_compression_trace
#print axioms singularTail_le_lowRankError
#print axioms real_best_rank_frobenius_attainment

end Reference.RealSVDPackage





