module

public import NLA.RA02.PaperKyFanWeights
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Complex.BigOperators

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper

theorem frame_projection_idempotent {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℂ)
    (hU : U.conjTranspose*U = 1) :
    (U*U.conjTranspose)*(U*U.conjTranspose) = U*U.conjTranspose := by
  calc
    _ = U*(U.conjTranspose*U)*U.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU,Matrix.mul_one]

theorem frame_complement_posSemidef {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℂ)
    (hU : U.conjTranspose*U = 1) : (1-U*U.conjTranspose).PosSemidef := by
  have hh : (1-U*U.conjTranspose).conjTranspose*(1-U*U.conjTranspose) = 1-U*U.conjTranspose := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      frame_projection_idempotent U hU]
    abel
  rw [← hh]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem frame_diagonal_weights {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℂ) (i : Fin n) :
    ((∑ j, Complex.normSq (U i j) : ℝ) : ℂ) = (U*U.conjTranspose) i i := by
  simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]
  rfl

theorem frame_weights_bounds {n m : ℕ} (U : Matrix (Fin n) (Fin m) ℂ)
    (hU : U.conjTranspose*U = 1) :
    (∀ i, 0 ≤ ∑ j, Complex.normSq (U i j) ∧ (∑ j, Complex.normSq (U i j)) ≤ 1) ∧
    (∑ i, ∑ j, Complex.normSq (U i j)) = (m : ℝ) := by
  constructor
  · intro i
    constructor
    · exact Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
    · have hp := (frame_complement_posSemidef U hU).diag_nonneg (i:=i)
      rw [Matrix.sub_apply, Matrix.one_apply_eq, ← frame_diagonal_weights U i] at hp
      have hr := (Complex.nonneg_iff.mp hp).1
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hr
      linarith
  · apply Complex.ofReal_injective
    rw [Complex.ofReal_sum]
    simp_rw [frame_diagonal_weights U]
    change (U*U.conjTranspose).trace = ((m : ℝ) : ℂ)
    rw [Matrix.trace_mul_comm, hU]
    simp

#print axioms frame_weights_bounds
end NLA.RA02.Paper
