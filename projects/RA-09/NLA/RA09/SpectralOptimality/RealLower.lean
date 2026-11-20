module

public import NLA.RA09.SpectralOptimality.Definitions
public import NLA.RA09.Paper.Rank
public import NLA.TR04.RealSVD.RealLower

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace RootRA09SpectralOptimality
open NLA.RA09

theorem real_combination_gram {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) :
    (spectralCombination d v).transpose * spectralCombination d v =
      spectralCombination d (fun i => (v i)^2) := by
  let Q : RealMatrix n := d.orthogonal
  have hQ := orthogonal_transpose_mul d.orthogonal
  change (Q * Matrix.diagonal v * Q.transpose).transpose * (Q * Matrix.diagonal v * Q.transpose) = _
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose]
  calc
    _ = Q * Matrix.diagonal v * (Q.transpose * Q) * Matrix.diagonal v * Q.transpose := by
      simp only [Matrix.mul_assoc]
    _ = Q * Matrix.diagonal (fun i => v i * v i) * Q.transpose := by
      rw [hQ,Matrix.mul_one,Matrix.mul_assoc Q,Matrix.diagonal_mul_diagonal]
    _ = _ := by simp only [spectralCombination, Q, pow_two]

theorem real_tail_le_compression {n q : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hdec : Antitone v)
    (k : ℕ) (hq : n-k ≤ q) (U : Matrix (Fin n) (Fin q) ℝ)
    (hU : U.transpose * U = 1) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), (v i)^2) ≤
      (U.transpose * ((spectralCombination d v).transpose * spectralCombination d v) * U).trace := by
  let Q : RealMatrix n := d.orthogonal
  let W : Matrix (Fin n) (Fin q) ℝ := Q.transpose * U
  have hW : W.transpose * W = 1 := by
    dsimp [W]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc
      _ = U.transpose * (Q * Q.transpose) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [orthogonal_mul_transpose d.orthogonal,Matrix.mul_one,hU]
  have hw := Reference.RealSVDPackage.frame_weights_bounds W hW
  have hsq : Antitone (fun i => (v i)^2) := by
    intro i j hij
    exact pow_le_pow_left₀ (hv j) (hdec hij) 2
  have hb := Reference.RealSVDPackage.ordered_weighted_tail_bound (fun i => (v i)^2)
    (fun i => ∑ j, W i j ^ 2) k hsq (fun i => sq_nonneg _) hw.1
    (by rw [Reference.RealSVDPackage.tail_index_card,hw.2]; exact_mod_cast hq)
  have he : U.transpose * ((spectralCombination d v).transpose * spectralCombination d v) * U =
      W.transpose * Matrix.diagonal (fun i => (v i)^2) * W := by
    rw [real_combination_gram]
    simp only [W,spectralCombination,Q,Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_assoc]
  rw [he,Reference.RealSVDPackage.frame_diagonal_compression_trace]
  exact hb

theorem real_spectral_lower {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) (hdec : Antitone v)
    (B : RealMatrix n) (k : ℕ) (hB : B.rank ≤ k) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), (v i)^2) ≤
      frobeniusSquared (spectralCombination d v - B) := by
  obtain ⟨q,U,hdim,hU,hBU⟩ := Reference.RealSVDPackage.exists_kernel_frame B k hB
  let C := spectralCombination d v
  have hEU : (C-B)*U = C*U := by rw [Matrix.sub_mul,hBU,sub_zero]
  have he : U.transpose*(C.transpose*C)*U = U.transpose*((C-B).transpose*(C-B))*U := by
    calc
      _ = (C*U).transpose*(C*U) := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
      _ = ((C-B)*U).transpose*((C-B)*U) := by rw [hEU]
      _ = _ := by simp only [Matrix.transpose_mul,Matrix.mul_assoc]
  have hb := real_tail_le_compression d v hv hdec k hdim U hU
  change _ ≤ (U.transpose*(C.transpose*C)*U).trace at hb
  rw [he] at hb
  exact hb.trans (Reference.RealSVDPackage.frobenius_compression_bound (C-B) U hU)

theorem actual_real_spectral_tail_lower {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (B : RealMatrix n) (k : ℕ) (hB : B.rank ≤ k) :
    spectralTail d k ≤ frobeniusSquared (A-B) := by
  have h := real_spectral_lower d d.eigenvalues d.nonnegative d.decreasing B k hB
  have he : spectralCombination d d.eigenvalues = A := d.reconstruct.symm
  simpa only [he,spectralTail] using h

theorem actual_real_function_tail_lower {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f) (B : RealMatrix n) (k : ℕ) (hB : B.rank ≤ k) :
    functionTail d f k ≤ frobeniusSquared (functionalCalculus f A-B) := by
  have h := real_spectral_lower d (fun i => f (d.eigenvalues i))
    (fun i => hf.2.2.1 _ (d.nonnegative i))
    (fun i j hij => hf.2.1 (d.nonnegative j) (d.nonnegative i) (d.decreasing hij)) B k hB
  simpa only [functionTail,selected_cfc_eq d f] using h

#print axioms actual_real_spectral_tail_lower
#print axioms actual_real_function_tail_lower
end RootRA09SpectralOptimality
