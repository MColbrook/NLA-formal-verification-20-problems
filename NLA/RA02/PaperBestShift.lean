module

public import NLA.RA02.PaperTailMonotone
public import NLA.RA02.PaperTailShift

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem gram_identity_shift {n : ℕ} (C : NLA.RA02.Square n) (hC : C.IsHermitian) (δ : ℝ) :
    (C+δ • 1).conjTranspose*(C+δ • 1) =
      C.conjTranspose*C + (2*δ) • C + δ^2 • 1 := by
  simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_smul,star_trivial,
    Matrix.conjTranspose_one,hC.eq,Matrix.add_mul,Matrix.mul_add,Matrix.smul_mul,
    Matrix.mul_smul,Matrix.mul_one,Matrix.one_mul,pow_two]
  module

theorem frame_gram_identity_shift_trace {n q : ℕ} (C : NLA.RA02.Square n)
    (hC : C.IsHermitian) (δ : ℝ) (U : Matrix (Fin n) (Fin q) ℂ)
    (hU : U.conjTranspose*U=1) :
    (U.conjTranspose*((C+δ • 1).conjTranspose*(C+δ • 1))*U).trace.re =
      (U.conjTranspose*(C.conjTranspose*C)*U).trace.re +
      2*δ*(U.conjTranspose*C*U).trace.re + δ^2*(q : ℝ) := by
  rw [gram_identity_shift C hC δ]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.mul_one,hU,Matrix.trace_add,Matrix.trace_smul,Complex.add_re,
    Complex.smul_re,smul_eq_mul]
  simp [Matrix.trace,Matrix.diag]

theorem best_error_identity_shift_bounds {n : ℕ} (C : NLA.RA02.Square n)
    (hC : C.PosSemidef) (r : ℕ) (hr : r ≤ n) (δ : ℝ) (hδ : 0 ≤ δ) :
    rectangularBestRankErrorSquared C r ≤ rectangularBestRankErrorSquared (C+δ • 1) r ∧
      rectangularBestRankErrorSquared (C+δ • 1) r ≤
        rectangularBestRankErrorSquared C r + 2*δ*NLA.RA02.realTrace C + δ^2*(n-r : ℕ) := by
  let A := C.conjTranspose*C
  let B := (C+δ • 1).conjTranspose*(C+δ • 1)
  have hA : A.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self C
  have hB : B.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self (C+δ • 1)
  have hBA : (B-A).PosSemidef := by
    have hp := (hC.smul (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hδ)).add
      (Matrix.PosSemidef.one.smul (sq_nonneg δ))
    have he : B-A = (2*δ) • C + δ^2 • 1 := by
      dsimp [A,B]
      rw [gram_identity_shift C hC.isHermitian δ]
      abel
    rw [he]
    exact hp
  simp only [rectangularBest_eq_gramTail,gramTail]
  constructor
  · exact rankTail_mono_psd A B hA hB hBA r hr
  · obtain ⟨U,hU,he⟩ := exists_rankTail_minimizer A hA r hr
    have hb := rankTail_le_compression_trace B hB r (le_refl _) U hU
    have hf := frame_gram_identity_shift_trace C hC.isHermitian δ U hU
    change (U.conjTranspose*B*U).trace.re =
      (U.conjTranspose*A*U).trace.re + 2*δ*(U.conjTranspose*C*U).trace.re + δ^2*(n-r : ℕ) at hf
    rw [he] at hf
    have hu := mul_le_mul_of_nonneg_left (frame_trace_le_realTrace C hC U hU)
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hδ)
    change NLA.RA02.rankTail B hB.isHermitian r ≤ _
    linarith

#print axioms best_error_identity_shift_bounds
end NLA.RA02.Paper
