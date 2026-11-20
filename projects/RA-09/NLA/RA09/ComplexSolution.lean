module

public import NLA.RA09.ComplexConclusions
public import NLA.RA09.ComplexDegenerate
public import NLA.RA09.ComplexHarmonicMatrix

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder ComplexOrder
open Matrix
namespace NLA.RA09.ComplexPaper

theorem paper_ordered_matrix_excess {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (hBA : B ≤ A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) - functionTail dA f k ≤
      (transferScale f (dA.eigenvalues ⟨k,hk⟩))^2 *
        (frobeniusSquared (A-B) - spectralTail dA k) := by
  apply ordered_matrix_excess <;> assumption

theorem paper_unordered_matrix_excess {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) - functionTail dA f k ≤
      2*(transferScale f (dA.eigenvalues ⟨k,hk⟩))^2 *
        (frobeniusSquared (A-B) - spectralTail dA k) := by
  apply unordered_matrix_excess <;> assumption

theorem paper_ordered_matrix_squared_relative {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (hBA : B ≤ A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (η : ℝ) (hη : 0 ≤ η) (hA : frobeniusSquared (A-B) ≤ (1+η)*spectralTail dA k) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+η)*functionTail dA f k := by
  apply ordered_matrix_squared_relative <;> assumption

theorem paper_unordered_matrix_squared_relative {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (η : ℝ) (hη : 0 ≤ η) (hA : frobeniusSquared (A-B) ≤ (1+η)*spectralTail dA k) :
    frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+2*η)*functionTail dA f k := by
  apply unordered_matrix_squared_relative <;> assumption

theorem paper_ordered_matrix_norm_relative {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (hBA : B ≤ A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hA : frobeniusNorm (A-B) ≤ (1+ε)*Real.sqrt (spectralTail dA k)) :
    frobeniusNorm (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+ε)*Real.sqrt (functionTail dA f k) := by
  apply ordered_matrix_norm_relative <;> assumption

theorem paper_unordered_matrix_norm_relative {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hA : frobeniusNorm (A-B) ≤ (1+ε)*Real.sqrt (spectralTail dA k)) :
    frobeniusNorm (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+2*ε)*Real.sqrt (functionTail dA f k) := by
  apply unordered_matrix_norm_relative <;> assumption

theorem paper_spectral_tail_zero_of_cutoff_zero {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) (hk : k < n)
    (hzero : d.eigenvalues ⟨k,hk⟩ = 0) : spectralTail d k = 0 := by
  apply spectral_tail_zero_of_cutoff_zero <;> assumption

theorem paper_spectral_tail_full {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) : spectralTail d n = 0 := by
  apply spectral_tail_full <;> assumption

theorem paper_zero_tail_residual_exact {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (k : ℕ) (hk : k ≤ n) (hB : B.rank ≤ k)
    (hzero : spectralTail dA k = 0) (η : ℝ)
    (herror : frobeniusSquared (A-B) ≤ (1+η)*spectralTail dA k) :
    A = B ∧ frobeniusSquared (functionalCalculus f A - functionTruncation dB f k) =
      functionTail dA f k := by
  apply zero_tail_residual_exact <;> assumption

theorem paper_complex_ordered_data_exists {n : ℕ} (A : ComplexMatrix n)
    (hA : A.PosSemidef) : Nonempty (OrderedSpectralData A) := by
  apply orderedSpectral_exists_proved <;> assumption

theorem paper_complex_frobenius_semantics {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    frobeniusSquared A = frobeniusNorm A ^ 2 := by
  apply frobeniusSquared_norm <;> assumption

theorem paper_complex_selected_cfc {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) :
    functionalCalculus f A = spectralCombination d (fun i => f (d.eigenvalues i)) := by
  apply selected_cfc_eq <;> assumption

theorem paper_complex_harmonic_matrix {n : ℕ} (A : ComplexMatrix n)
    (v : Fin n → ℂ) (b : ℝ) (hb : 0 < b)
    (horder : (b : ℂ) • Matrix.vecMulVec v (star v) ≤ A) :
    IsMoorePenroseInverse A (spectralPseudoinverse A) ∧
      v ∈ Set.range (fun x : Fin n → ℂ => A *ᵥ x) ∧
      (b : ℂ) * (star v ⬝ᵥ (spectralPseudoinverse A *ᵥ v)) ≤ 1 := by
  apply harmonic_matrix_full <;> assumption

#print axioms paper_ordered_matrix_excess
#print axioms paper_unordered_matrix_excess
#print axioms paper_ordered_matrix_squared_relative
#print axioms paper_unordered_matrix_squared_relative
#print axioms paper_ordered_matrix_norm_relative
#print axioms paper_unordered_matrix_norm_relative
#print axioms paper_spectral_tail_zero_of_cutoff_zero
#print axioms paper_spectral_tail_full
#print axioms paper_zero_tail_residual_exact
#print axioms paper_complex_ordered_data_exists
#print axioms paper_complex_frobenius_semantics
#print axioms paper_complex_selected_cfc
#print axioms paper_complex_harmonic_matrix
end NLA.RA09.ComplexPaper
