module

public import NLA.RA09.PaperDefinitions
public import Mathlib.Analysis.Complex.Norm

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder
namespace NLA.RA09.ComplexPaper

abbrev ComplexMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def frobeniusSquared {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

section
open scoped Matrix.Norms.Frobenius
def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ := ‖A‖
end

/-- Actual complex unitary eigenbasis, with any choice within repeated eigenspaces. -/
structure OrderedSpectralData {n : ℕ} (A : ComplexMatrix n) where
  eigenvalues : Fin n → ℝ
  unitary : Matrix.unitaryGroup (Fin n) ℂ
  decreasing : Antitone eigenvalues
  nonnegative : ∀ i, 0 ≤ eigenvalues i
  reconstruct : A = (unitary : ComplexMatrix n) *
    Matrix.diagonal (fun i => (eigenvalues i : ℂ)) * (unitary : ComplexMatrix n).conjTranspose

def spectralCombination {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (u : Fin n → ℝ) : ComplexMatrix n :=
  (d.unitary : ComplexMatrix n) * Matrix.diagonal (fun i => (u i : ℂ)) *
    (d.unitary : ComplexMatrix n).conjTranspose

def functionalCalculus {n : ℕ} (f : ℝ → ℝ) (A : ComplexMatrix n) : ComplexMatrix n :=
  cfc (R := ℝ) f A

def truncation {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) (k : ℕ) :=
  spectralCombination d (fun i => if i.val < k then d.eigenvalues i else 0)

def functionTruncation {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (k : ℕ) :=
  spectralCombination d (fun i => if i.val < k then f (d.eigenvalues i) else 0)

def spectralTail {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), d.eigenvalues i ^ 2

def functionTail {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), f (d.eigenvalues i) ^ 2

def overlapUnitary {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) :
    Matrix.unitaryGroup (Fin n) ℂ := star dA.unitary * dB.unitary

def overlapWeights {n : ℕ} {A B : ComplexMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B) (i j : Fin n) : ℝ :=
  Complex.normSq ((overlapUnitary dA dB : ComplexMatrix n) i j)

end NLA.RA09.ComplexPaper
