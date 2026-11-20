module

/- Matrix Ky Fan lower-tail estimate supporting the universal random-pivoting
bounds. Formalization of the variational step used in CETW25, Section 5.4,
and Gilles--Wilber arXiv:2601.22344, Appendix A.1. -/
public import NLA.RA02.PaperProjectionWeights
public import NLA.RA02.SpectralTail
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper

theorem frame_diagonal_compression_trace {n m : ℕ} (d : Fin n → ℝ)
    (U : Matrix (Fin n) (Fin m) ℂ) :
    (U.conjTranspose * Matrix.diagonal (fun i => (d i : ℂ)) * U).trace.re =
      ∑ i, d i * ∑ j, Complex.normSq (U i j) := by
  have hh : (U.conjTranspose * Matrix.diagonal (fun i => (d i : ℂ)) * U).trace =
      ∑ i, (d i : ℂ) * ((∑ j, Complex.normSq (U i j) : ℝ) : ℂ) := by
    rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [frame_diagonal_weights]
  have hr := congrArg Complex.re hh
  simpa only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re] using hr

theorem tail_index_card (n r : ℕ) :
    (Finset.univ.filter (fun i : Fin n => r ≤ i.val)).card = n-r := by
  by_cases hr : r < n
  · have he : Finset.univ.filter (fun i : Fin n => r ≤ i.val) = Finset.Ici (⟨r,hr⟩ : Fin n) := by
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

theorem rankTail_le_compression_trace {n m : ℕ} (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) (r : ℕ) (hm : n-r ≤ m)
    (U : Matrix (Fin n) (Fin m) ℂ) (hU : U.conjTranspose*U = 1) :
    NLA.RA02.rankTail A hA.isHermitian r ≤ (U.conjTranspose*A*U).trace.re := by
  let V := hA.isHermitian.eigenvectorUnitary
  let W : Matrix (Fin n) (Fin m) ℂ := (V : NLA.RA02.Square n).conjTranspose*U
  have hV : (V : NLA.RA02.Square n)*(V : NLA.RA02.Square n).conjTranspose = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self V
  have hW : W.conjTranspose*W = 1 := by
    dsimp [W]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = U.conjTranspose * ((V : NLA.RA02.Square n)*(V : NLA.RA02.Square n).conjTranspose)*U := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV, Matrix.mul_one, hU]
  let w : Fin n → ℝ := fun i => ∑ j, Complex.normSq (W (NLA.RA02.eigenvalueReindex n i) j)
  have hw := frame_weights_bounds W hW
  have hsum : (∑ i, w i) = (m : ℝ) := by
    change (∑ i, (fun i => ∑ j, Complex.normSq (W i j)) (NLA.RA02.eigenvalueReindex n i)) = _
    exact ((NLA.RA02.eigenvalueReindex n).sum_comp (fun i : Fin n => ∑ j, Complex.normSq (W i j))).trans hw.2
  have hb := ordered_weighted_tail_bound (NLA.RA02.orderedEigenvalues A hA.isHermitian) w r
    (NLA.RA02.orderedEigenvalues_antitone A hA.isHermitian) (NLA.RA02.orderedEigenvalues_nonneg A hA)
    (fun i => hw.1 (NLA.RA02.eigenvalueReindex n i)) (by rw [tail_index_card,hsum]; exact_mod_cast hm)
  change NLA.RA02.rankTail A hA.isHermitian r ≤ _ at hb
  have hspec : A = (V : NLA.RA02.Square n) *
      Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) *
      (V : NLA.RA02.Square n).conjTranspose := by
    simpa [V, Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hA.isHermitian.spectral_theorem
  have he : U.conjTranspose*A*U = W.conjTranspose*
      Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ))*W := by
    conv_lhs => rw [hspec]
    simp [W, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he, frame_diagonal_compression_trace]
  calc
    NLA.RA02.rankTail A hA.isHermitian r ≤ ∑ i, NLA.RA02.orderedEigenvalues A hA.isHermitian i*w i := hb
    _ = ∑ i, hA.isHermitian.eigenvalues i * ∑ j, Complex.normSq (W i j) := by
      simp only [NLA.RA02.orderedEigenvalues_eq_reindexed, w]
      exact (NLA.RA02.eigenvalueReindex n).sum_comp
        (fun i : Fin n => hA.isHermitian.eigenvalues i * ∑ j, Complex.normSq (W i j))

#print axioms rankTail_le_compression_trace
end NLA.RA02.Paper
