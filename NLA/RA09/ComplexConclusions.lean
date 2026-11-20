module

/- Complex-field adaptation of the full paper relative-error conclusions. -/
public import NLA.RA09.ComplexUnordered
public import NLA.RA09.ComplexTransfer
public import NLA.RA09.ComplexRank

@[expose] public section

/-! The paper's rank-at-most-k matrix error bounds and both relative-error
conventions. The sharpness assertions are separate proof obligations. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder ComplexOrder
namespace NLA.RA09.ComplexPaper

open scoped Matrix.Norms.Frobenius in
private theorem frobeniusNorm_nonneg {n : ℕ} (M : ComplexMatrix n) :
    0 ≤ frobeniusNorm M := by
  exact norm_nonneg M

theorem ordered_matrix_excess {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (hBA : B ≤ A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) - functionTail dA f k ≤
      (transferScale f (dA.eigenvalues ⟨k,hk⟩))^2 *
        (frobeniusSquared (A-B) - spectralTail dA k) := by
  simpa only [truncation_eq_of_rank_le dB k hk.le hB] using
    (positive_tail_transfer_proved dA dB hBA f hf k hk hτ).1

theorem unordered_matrix_excess {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) - functionTail dA f k ≤
      2*(transferScale f (dA.eigenvalues ⟨k,hk⟩))^2 *
        (frobeniusSquared (A-B) - spectralTail dA k) := by
  simpa only [truncation_eq_of_rank_le dB k hk.le hB] using
    unordered_positive_tail_transfer dA dB f hf k hk hτ

private theorem squared_relative_transfer (EA EF TA TF c α η : ℝ)
    (hα : 0 ≤ α) (hη : 0 ≤ η) (hE : EF-TF ≤ α*c^2*(EA-TA))
    (hT : c^2*TA ≤ TF) (hA : EA ≤ (1+η)*TA) : EF ≤ (1+α*η)*TF := by
  have h1 := mul_le_mul_of_nonneg_left
    (show EA-TA ≤ η*TA by nlinarith) (mul_nonneg hα (sq_nonneg c))
  have h2 := mul_le_mul_of_nonneg_left hT (mul_nonneg hα hη)
  nlinarith

theorem ordered_matrix_squared_relative {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (hBA : B ≤ A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (η : ℝ) (hη : 0 ≤ η) (hA : frobeniusSquared (A-B) ≤ (1+η)*spectralTail dA k) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+η)*functionTail dA f k := by
  have hE := ordered_matrix_excess dA dB hBA f hf k hk hB hτ
  have hT := spectral_tail_scaling dA f hf k hk hτ
  simpa only [one_mul] using squared_relative_transfer _ _ _ _ _ 1 η
    (by norm_num) hη (by simpa only [one_mul] using hE) hT hA

theorem unordered_matrix_squared_relative {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (η : ℝ) (hη : 0 ≤ η) (hA : frobeniusSquared (A-B) ≤ (1+η)*spectralTail dA k) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+2*η)*functionTail dA f k := by
  exact squared_relative_transfer _ _ _ _ _ 2 η (by norm_num) hη
    (unordered_matrix_excess dA dB f hf k hk hB hτ)
    (spectral_tail_scaling dA f hf k hk hτ) hA

private theorem norm_relative_transfer (x y TA TF α ε : ℝ)
    (hx : 0 ≤ x) (hTA : 0 ≤ TA) (hTF : 0 ≤ TF) (hα : 1 ≤ α) (hε : 0 ≤ ε)
    (htransfer : ∀ η : ℝ, 0 ≤ η → x^2 ≤ (1+η)*TA → y^2 ≤ (1+α*η)*TF)
    (hpremise : x ≤ (1+ε)*Real.sqrt TA) : y ≤ (1+α*ε)*Real.sqrt TF := by
  have hsq : x^2 ≤ (1+ε)^2*TA := by
    simpa only [← pow_two, mul_pow, Real.sq_sqrt hTA] using mul_self_le_mul_self hx hpremise
  have hη : 0 ≤ (1+ε)^2-1 := by nlinarith
  have h := htransfer ((1+ε)^2-1) hη (by nlinarith [hsq])
  apply le_of_sq_le_sq ?_ (mul_nonneg (by positivity) (Real.sqrt_nonneg _))
  rw [mul_pow, Real.sq_sqrt hTF]
  have hgain : 0 ≤ ((1+α*ε)^2-(1+α*((1+ε)^2-1)))*TF := by
    have hid : ((1+α*ε)^2-(1+α*((1+ε)^2-1)))*TF = α*(α-1)*ε^2*TF := by ring
    rw [hid]
    exact mul_nonneg (mul_nonneg (mul_nonneg (show 0 ≤ α by linarith)
      (sub_nonneg.mpr hα)) (sq_nonneg ε)) hTF
  nlinarith

theorem ordered_matrix_norm_relative {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (hBA : B ≤ A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hA : frobeniusNorm (A-B) ≤ (1+ε)*Real.sqrt (spectralTail dA k)) :
    frobeniusNorm (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+ε)*Real.sqrt (functionTail dA f k) := by
  have hTA : 0 ≤ spectralTail dA k := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hTF : 0 ≤ functionTail dA f k := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h := norm_relative_transfer (frobeniusNorm (A-B))
    (frobeniusNorm (functionalCalculus f A-functionTruncation dB f k))
    (spectralTail dA k) (functionTail dA f k) 1 ε
    (frobeniusNorm_nonneg _) hTA hTF le_rfl hε ?_ hA
  · simpa only [one_mul] using h
  · intro η hη hp
    rw [← frobeniusSquared_norm] at hp ⊢
    simpa only [one_mul] using ordered_matrix_squared_relative dA dB hBA f hf k hk hB hτ η hη hp

theorem unordered_matrix_norm_relative {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hA : frobeniusNorm (A-B) ≤ (1+ε)*Real.sqrt (spectralTail dA k)) :
    frobeniusNorm (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+2*ε)*Real.sqrt (functionTail dA f k) := by
  apply norm_relative_transfer (frobeniusNorm (A-B))
    (frobeniusNorm (functionalCalculus f A-functionTruncation dB f k))
    (spectralTail dA k) (functionTail dA f k) 2 ε (frobeniusNorm_nonneg _)
    (Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    (by norm_num) hε ?_ hA
  intro η hη hp
  rw [← frobeniusSquared_norm] at hp ⊢
  exact unordered_matrix_squared_relative dA dB f hf k hk hB hτ η hη hp

#print axioms ordered_matrix_excess
#print axioms unordered_matrix_excess
#print axioms ordered_matrix_squared_relative
#print axioms unordered_matrix_squared_relative
#print axioms ordered_matrix_norm_relative
#print axioms unordered_matrix_norm_relative

end NLA.RA09.ComplexPaper
