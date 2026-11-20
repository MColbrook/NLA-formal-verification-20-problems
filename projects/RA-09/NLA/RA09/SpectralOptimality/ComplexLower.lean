module

public import NLA.RA09.SpectralOptimality.Definitions
public import NLA.RA09.ComplexRank
public import NLA.RA02.PaperKernelFrame

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix ComplexOrder
namespace RootRA09SpectralOptimality
open NLA.RA09.ComplexPaper

theorem complex_combination_gram {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) :
    (spectralCombination d v).conjTranspose * spectralCombination d v =
      spectralCombination d (fun i => (v i)^2) := by
  let Q : ComplexMatrix n := d.unitary
  have hQ := unitary_star_mul d.unitary
  have hd : (Matrix.diagonal (fun i => (v i : ℂ))).conjTranspose =
      Matrix.diagonal (fun i => (v i : ℂ)) := by
    simp [Matrix.diagonal_conjTranspose,Pi.star_def]
  change (Q * Matrix.diagonal (fun i => (v i : ℂ)) * Q.conjTranspose).conjTranspose *
    (Q * Matrix.diagonal (fun i => (v i : ℂ)) * Q.conjTranspose) = _
  rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hd]
  calc
    _ = Q * Matrix.diagonal (fun i => (v i : ℂ)) * (Q.conjTranspose * Q) *
        Matrix.diagonal (fun i => (v i : ℂ)) * Q.conjTranspose := by simp only [Matrix.mul_assoc]
    _ = Q * Matrix.diagonal (fun i => (v i : ℂ) * (v i : ℂ)) * Q.conjTranspose := by
      rw [hQ,Matrix.mul_one,Matrix.mul_assoc Q,Matrix.diagonal_mul_diagonal]
    _ = _ := by simp only [spectralCombination,Q,pow_two,Complex.ofReal_mul]

theorem complex_tail_le_compression {n q : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hdec : Antitone v)
    (k : ℕ) (hq : n-k ≤ q) (U : Matrix (Fin n) (Fin q) ℂ)
    (hU : U.conjTranspose * U = 1) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), (v i)^2) ≤
      (U.conjTranspose * ((spectralCombination d v).conjTranspose * spectralCombination d v) * U).trace.re := by
  let Q : ComplexMatrix n := d.unitary
  let W : Matrix (Fin n) (Fin q) ℂ := Q.conjTranspose * U
  have hW : W.conjTranspose * W = 1 := by
    dsimp [W]
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
    calc
      _ = U.conjTranspose * (Q * Q.conjTranspose) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [unitary_mul_star d.unitary,Matrix.mul_one,hU]
  have hw := NLA.RA02.Paper.frame_weights_bounds W hW
  have hsq : Antitone (fun i => (v i)^2) := by
    intro i j hij
    exact pow_le_pow_left₀ (hv j) (hdec hij) 2
  have hb := NLA.RA02.Paper.ordered_weighted_tail_bound (fun i => (v i)^2)
    (fun i => ∑ j, Complex.normSq (W i j)) k hsq (fun i => sq_nonneg _) hw.1
    (by rw [NLA.RA02.Paper.tail_index_card,hw.2]; exact_mod_cast hq)
  have he : U.conjTranspose * ((spectralCombination d v).conjTranspose * spectralCombination d v) * U =
      W.conjTranspose * Matrix.diagonal (fun i => (((v i)^2 : ℝ) : ℂ)) * W := by
    rw [complex_combination_gram]
    simp only [W,spectralCombination,Q,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  rw [he,NLA.RA02.Paper.frame_diagonal_compression_trace]
  exact hb

theorem complex_spectral_lower {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hdec : Antitone v)
    (B : ComplexMatrix n) (k : ℕ) (hB : B.rank ≤ k) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), (v i)^2) ≤
      frobeniusSquared (spectralCombination d v-B) := by
  obtain ⟨q,U,hdim,hU,hBU⟩ := NLA.RA02.Paper.exists_kernel_frame B k hB
  let C := spectralCombination d v
  have hEU : (C-B)*U = C*U := by rw [Matrix.sub_mul,hBU,sub_zero]
  have he : U.conjTranspose*(C.conjTranspose*C)*U = U.conjTranspose*((C-B).conjTranspose*(C-B))*U := by
    calc
      _ = (C*U).conjTranspose*(C*U) := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = ((C-B)*U).conjTranspose*((C-B)*U) := by rw [hEU]
      _ = _ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  have hb := complex_tail_le_compression d v hv hdec k hdim U hU
  change _ ≤ (U.conjTranspose*(C.conjTranspose*C)*U).trace.re at hb
  rw [he] at hb
  exact hb.trans (NLA.RA02.Paper.frobenius_compression_bound (C-B) U hU)

theorem actual_complex_spectral_tail_lower {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (B : ComplexMatrix n) (k : ℕ) (hB : B.rank ≤ k) :
    spectralTail d k ≤ frobeniusSquared (A-B) := by
  have h := complex_spectral_lower d d.eigenvalues d.nonnegative d.decreasing B k hB
  have he : spectralCombination d d.eigenvalues = A := d.reconstruct.symm
  simpa only [he,spectralTail] using h

theorem actual_complex_function_tail_lower {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (f : ℝ → ℝ) (hf : NLA.RA09.PaperAdmissibleFunction f) (B : ComplexMatrix n) (k : ℕ) (hB : B.rank ≤ k) :
    functionTail d f k ≤ frobeniusSquared (functionalCalculus f A-B) := by
  have h := complex_spectral_lower d (fun i => f (d.eigenvalues i))
    (fun i => hf.2.2.1 _ (d.nonnegative i))
    (fun i j hij => hf.2.1 (d.nonnegative j) (d.nonnegative i) (d.decreasing hij)) B k hB
  simpa only [functionTail,selected_cfc_eq d f] using h

#print axioms actual_complex_spectral_tail_lower
#print axioms actual_complex_function_tail_lower
end RootRA09SpectralOptimality
