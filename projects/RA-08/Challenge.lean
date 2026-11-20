module

public import Mathlib

@[expose] public section

/-!
Standalone statement surface for RA-08.
Definitions and selected theorem types are retained from the original sources.
Historical notices below are preserved; current review status is in the audit records.
-/


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.Definitions -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Proof-independent statement boundary for Matthew J. Colbrook's RA-08
counterexample. Formalization affiliation: Department of Computing and
Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA. No theorem implementation is imported here.
-/








set_option autoImplicit false
open scoped BigOperators Classical MatrixOrder
noncomputable section

namespace NLA.RA08

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The actual operator norm for the matrix acting on real Euclidean space.
This is not the default norm on a matrix or on a function space. -/
def spectralNorm {n : ℕ} (A : RealMatrix n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖

/-- Exactly the function class in the canonical problem. A function on the
nonnegative half-line is represented by an arbitrary real extension. Values
at negative arguments are unconstrained; no `f 0 = 0` premise is imposed. -/
def AdmissibleFunction (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) f ∧
    MonotoneOn f (Set.Ici 0) ∧ ∀ x : ℝ, 0 ≤ x → 0 ≤ f x

/-- An arbitrary complete ordered orthonormal eigendecomposition of the
actual matrix. Over the reals a unitary matrix is an orthogonal matrix.
Both the nonnegative eigenvalues and every permitted choice of eigenvectors
are quantified in the conjecture; no preferred choice is built in.
Reconstruction, not a claimed numerical spectrum, is part of the data. -/
structure OrderedSpectralData {n : ℕ} (A : RealMatrix n) where
  eigenvalues : Fin n → ℝ
  orthogonal : Matrix.unitaryGroup (Fin n) ℝ
  decreasing : Antitone eigenvalues
  nonnegative : ∀ i, 0 ≤ eigenvalues i
  reconstruct : A =
    (orthogonal : RealMatrix n) * Matrix.diagonal eigenvalues *
      (orthogonal : RealMatrix n).transpose

/-- Apply arbitrary scalar values in the selected eigenbasis. -/
def spectralCombination {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (values : Fin n → ℝ) : RealMatrix n :=
  (d.orthogonal : RealMatrix n) * Matrix.diagonal values *
    (d.orthogonal : RealMatrix n).transpose

/-- Canonical rank-`k` eigenvalue truncation, zero-based indices `i < k`. -/
def truncation {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) : RealMatrix n :=
  spectralCombination d (fun i => if i.val < k then d.eigenvalues i else 0)

/-- Genuine real continuous functional calculus in the real matrix algebra. -/
def functionalCalculus {n : ℕ} (f : ℝ → ℝ) (A : RealMatrix n) : RealMatrix n :=
  cfc (R := ℝ) f A

/-- The function truncation uses the SAME selected eigenvectors as `truncation`.
It is neither `f (X_k)` nor an independently rotated spectral truncation of `f X`.
In particular the discarded entries are zero even when `f 0` is positive. -/
def functionTruncation {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (k : ℕ) : RealMatrix n :=
  spectralCombination d (fun i => if i.val < k then f (d.eigenvalues i) else 0)

/-- Complete original RA-08 assertion, including every real symmetric PSD pair,
every original dimension/rank/error parameter, every admissible scalar function,
and every allowed ordered eigendecomposition. The matrix order is PSD order. -/
def ConcaveSpectralTransferConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
    ∀ A Ahat : RealMatrix n, A.PosSemidef → Ahat.PosSemidef → Ahat ≤ A →
      ∀ f : ℝ → ℝ, AdmissibleFunction f →
        ∀ dA : OrderedSpectralData A, ∀ dAhat : OrderedSpectralData Ahat,
          ∀ ε : ℝ, 0 ≤ ε →
            spectralNorm (A - truncation dAhat k) ≤
                (1 + ε) * spectralNorm (A - truncation dA k) →
            spectralNorm (functionalCalculus f A - functionTruncation dAhat f k) ≤
                (1 + ε) *
                  spectralNorm (functionalCalculus f A - functionTruncation dA f k)

/-- Colbrook's unchanged kink function, restricted to the half-line in the problem. -/
def witnessFunction (x : ℝ) : ℝ := min x 1

def witnessT : ℝ := 1 / 65536

def witnessA : ℝ := 17 / 16

def witnessB : ℝ := 127 / 128

/-- The source's exact two orthonormal columns. -/
def witnessU : Matrix (Fin 3) (Fin 2) ℝ :=
  (1 / 9 : ℝ) • !![1, 8; 8, 1; -4, 4]

/-- The unchanged rank-three orthogonal projection, written with the single
common denominator `65 * 81`. The source gives the equivalent `U Uᵀ` block form. -/
def witnessF : RealMatrix 6 :=
  (1 / 5265 : ℝ) •
    !![4160, 1024, 1792, 72, 576, 0;
       1024, 4160, -1792, 576, 72, 0;
       1792, -1792, 2048, -288, 288, 0;
       72, 576, -288, 81, 0, 0;
       576, 72, 288, 0, 81, 0;
       0, 0, 0, 0, 0, 5265]

def witnessApproximation : RealMatrix 6 :=
  Matrix.diagonal ![1 / 2, witnessB, witnessA, 0, 0, 0]

def witnessMatrix : RealMatrix 6 :=
  witnessApproximation + witnessT • witnessF

/-- The exact CFC image of the approximation is a conclusion to be proved. -/
def witnessApproximationImage : RealMatrix 6 :=
  Matrix.diagonal ![1 / 2, witnessB, 1, 0, 0, 0]

/-- An unnormalized vector avoids every numerical square-root computation. -/
def witnessVector : Fin 6 → ℝ := ![4, 3, 1, 0, 0, 0]

def minorantCoefficient : ℝ := 67108864 / 1896129

/-- A new exact proof route for the unchanged source witness. This polynomial
is a scalar minorant only on the spectral set that must actually be proved. -/
def minorantFunction (x : ℝ) : ℝ :=
  x - minorantCoefficient * x ^ 2 * (x - 1 / 2) ^ 2 * (x - witnessB) ^ 2

/-- Three commuting matrix factors. Its application to one vector is the
only degree-three matrix-vector computation required by the rational certificate. -/
def matrixK {n : ℕ} (A : RealMatrix n) : RealMatrix n :=
  A * (A - (1 / 2 : ℝ) • (1 : RealMatrix n)) *
    (A - witnessB • (1 : RealMatrix n))

/-- Named polynomial matrix expression; its equality with genuine CFC is a
proof obligation, not a definition of the continuous functional calculus. -/
def minorantMatrix {n : ℕ} (A : RealMatrix n) : RealMatrix n :=
  A - minorantCoefficient • (matrixK A) ^ 2

/-- Exact expected result of the three matrix-vector products. -/
def witnessKVector : Fin 6 → ℝ :=
  ![-119989013011 / 10452232411545600,
    2434900073263 / 167235718584729600,
    1756776553030423 / 41808929646182400,
    -24520157 / 743269860376576,
    14703909709 / 445961916225945600,
    0]

/-- A weaker strict gap than the manuscript's contour estimate, sufficient
for the complete original negative answer. It will use a material, explicit
kernel-only LeanCert point certificate, not an eigenvalue interval computation. -/
def witnessGap : ℝ :=
  78605142319958855341529309 / 11432529876841442781954048000

end NLA.RA08
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.PaperDefinitions -/



/- Proof-independent definitions of the paper's fixed Nyström sketch. -/
set_option autoImplicit false
open Matrix
noncomputable section
namespace NLA.RA08.Paper

def paperOmega : Matrix (Fin 6) (Fin 3) ℝ :=
  !![1,0,0; 0,1,0; 0,0,1; -8/9,-64/9,32/9; -64/9,-8/9,-32/9; 0,0,0]

def nystrom {n l : ℕ} (A : RealMatrix n) (Ω : Matrix (Fin n) (Fin l) ℝ) :
    RealMatrix n := A * Ω * (Ω.transpose * A * Ω)⁻¹ * Ω.transpose * A

end NLA.RA08.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: PaperChallenge -/


set_option autoImplicit false
noncomputable section
open scoped MatrixOrder
open Matrix
namespace NLA.RA08.Paper

theorem paper_spectral_failure (C : ℝ) (dA : OrderedSpectralData witnessMatrix) :
    spectralNorm (witnessMatrix - witnessApproximation) ≤
      (1 + (0 : ℝ)) * spectralNorm (witnessMatrix - truncation dA 3) ∧
    ¬ (spectralNorm (functionalCalculus witnessFunction witnessMatrix -
          functionalCalculus witnessFunction witnessApproximation) ≤
        (1 + C * 0) * spectralNorm (functionalCalculus witnessFunction witnessMatrix -
          functionTruncation dA witnessFunction 3)) := by
  sorry

end NLA.RA08.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.PaperDerivativeDefinitions -/


set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.RA08.Paper

/-- The printed divided difference, including both diagonal cases away from one. -/
def clippingDividedDifference (x y : ℝ) : ℝ :=
  if x = y then (if x < 1 then 1 else 0)
  else (witnessFunction x-witnessFunction y)/(x-y)

def clippingDerivative {n : ℕ} (b : Fin n → ℝ) (E : RealMatrix n) : RealMatrix n :=
  fun i j => clippingDividedDifference (b i) (b j)*E i j

def matrixAbsolute {n : ℕ} (A : RealMatrix n) : RealMatrix n := functionalCalculus abs A

def frobeniusSquared {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

open scoped Matrix.Norms.Frobenius in
def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ‖A‖

def diagonalSylvesterInverse {n : ℕ} (a : Fin n → ℝ) (F : RealMatrix n) : RealMatrix n :=
  fun i j => F i j/(a i+a j)

end NLA.RA08.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.PaperNuclearDefinitions -/



set_option autoImplicit false
noncomputable section
open scoped Classical Matrix
namespace NLA.RA08.Paper

/-- The actual nuclear norm: the trace of the positive square root of AᵀA. -/
def nuclearNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  (functionalCalculus Real.sqrt (A.transpose*A)).trace

def nuclearHeight {m : ℕ} (i : Fin m) : ℝ := (1/4 : ℝ)^(i.val+1)

def nuclearBaseEntries (m : ℕ) : Fin (m+m) → ℝ :=
  fun i => Sum.elim (fun j => 1-nuclearHeight j) (fun j => 1+nuclearHeight j)
    ((finSumFinEquiv (m := m) (n := m)).symm i)

def nuclearBase (m : ℕ) : RealMatrix (m+m) := Matrix.diagonal (nuclearBaseEntries m)

def nuclearUnitVector (m : ℕ) : Fin (m+m) → ℝ := fun _ => (Real.sqrt (2*m : ℝ))⁻¹

def nuclearPerturbation (m : ℕ) : RealMatrix (m+m) :=
  fun i j => nuclearUnitVector m i*nuclearUnitVector m j

/-- The actual derivative, rather than an assumed or numerically supplied matrix. -/
def nuclearDerivative (m : ℕ) : RealMatrix (m+m) :=
  clippingDerivative (nuclearBaseEntries m) (nuclearPerturbation m)

def nuclearKernel (m : ℕ) : RealMatrix m :=
  fun i j => nuclearHeight i/(nuclearHeight i+nuclearHeight j)

def nuclearTriangular (m : ℕ) : RealMatrix m := fun i j => if i ≤ j then 1 else 0

/-- The printed block expression, whose equality with the actual derivative is
    a separate proof obligation. Indices are reordered by the standard finite sum. -/
def nuclearDisplayedDerivative (m : ℕ) : RealMatrix (m+m) :=
  (1/(2*m) : ℝ) •
    (Matrix.fromBlocks (fun (_ _ : Fin m) => (1 : ℝ)) (nuclearKernel m)
      (nuclearKernel m).transpose (0 : RealMatrix m)).submatrix
      (finSumFinEquiv (m := m) (n := m)).symm
      (finSumFinEquiv (m := m) (n := m)).symm

end NLA.RA08.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.PaperNuclearNystromDefinitions -/



set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def nuclearLiftBaseEntries (m : ℕ) : Fin (m+m+1) → ℝ :=
  Fin.snoc (nuclearBaseEntries m) 0

def nuclearLiftBase (m : ℕ) : RealMatrix (m+m+1) :=
  Matrix.diagonal (nuclearLiftBaseEntries m)

def nuclearLiftVector (m : ℕ) (η : ℝ) : Fin (m+m+1) → ℝ :=
  Fin.snoc (fun i => Real.sqrt η*nuclearUnitVector m i) (Real.sqrt (1-η))

def nuclearLiftPerturbation (m : ℕ) (η : ℝ) : RealMatrix (m+m+1) :=
  Matrix.vecMulVec (nuclearLiftVector m η) (nuclearLiftVector m η)

def nuclearLiftA (m : ℕ) (η t : ℝ) : RealMatrix (m+m+1) :=
  nuclearLiftBase m+t • nuclearLiftPerturbation m η

/-- The printed sketch, with sqrt(eta)/sqrt(1-eta) in the last row. -/
def nuclearLiftSketch (m : ℕ) (η : ℝ) : Matrix (Fin (m+m+1)) (Fin (m+m)) ℝ :=
  Fin.snoc (1 : RealMatrix (m+m))
    (fun j => -(Real.sqrt η/Real.sqrt (1-η))*nuclearUnitVector m j)

def nuclearLiftAOmega (m : ℕ) : Matrix (Fin (m+m+1)) (Fin (m+m)) ℝ :=
  Fin.snoc (nuclearBase m) 0

def nuclearBaseInverse (m : ℕ) : RealMatrix (m+m) :=
  Matrix.diagonal (fun i => (nuclearBaseEntries m i)⁻¹)

end NLA.RA08.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.PaperNuclearTailDefinitions -/


set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def nuclearLiftTailLower (η t : ℝ) : ℝ := (1-η)*t-2*η*(1-η)*t^2

/-- The infimum of the actual finite real spectrum. -/
def nuclearLiftSmallest (m : ℕ) (η t : ℝ) : ℝ :=
  sInf (spectrum ℝ (nuclearLiftA m η t))

end NLA.RA08.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.PaperNuclearLiftDerivativeDefinitions -/


set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def nuclearLiftDerivative (m : ℕ) (η : ℝ) : RealMatrix (m+m+1) :=
  clippingDerivative (nuclearLiftBaseEntries m) (nuclearLiftPerturbation m η)

def nuclearLiftOutput (m : ℕ) (η t : ℝ) : RealMatrix (m+m+1) :=
  functionalCalculus witnessFunction (nuclearLiftA m η t)-
    functionalCalculus witnessFunction (nuclearLiftBase m)

end NLA.RA08.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.PaperNuclearSignDefinitions -/


set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def realSign (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

end NLA.RA08.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.PaperNuclearLiftTraceDefinitions -/



set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

def nuclearLiftUnitary {n : ℕ} (R : RealMatrix n) : RealMatrix (n+1) :=
  (Matrix.fromBlocks R 0 0 (1 : RealMatrix 1)).submatrix
    (finSumFinEquiv (m := n) (n := 1)).symm
    (finSumFinEquiv (m := n) (n := 1)).symm

end NLA.RA08.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.PaperNuclearCounterexampleDefinitions -/



set_option autoImplicit false
open scoped Matrix
noncomputable section
namespace NLA.RA08.Paper

/-- The printed nuclear theorem, with actual Nyström and actual ordered truncations. -/
def NuclearTransferFailure (C ε₀ : ℝ) : Prop :=
  ∃ (n l k : ℕ) (A : RealMatrix n) (Ω : Matrix (Fin n) (Fin l) ℝ)
      (d : OrderedSpectralData A) (ε : ℝ),
    A.PosDef ∧ Function.Injective (fun x => Ω *ᵥ x) ∧
    k=(nystrom A Ω).rank ∧ 0 < ε ∧ ε < ε₀ ∧
    nuclearNorm (A-nystrom A Ω)=(1+ε)*nuclearNorm (A-truncation d k) ∧
    nuclearNorm (functionalCalculus witnessFunction A-
      functionalCalculus witnessFunction (nystrom A Ω)) >
        (1+C*ε)*nuclearNorm (functionalCalculus witnessFunction A-
          functionTruncation d witnessFunction k)

end NLA.RA08.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA08.NuclearCounterexampleChallenge -/


set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem verified_paper_nuclear_counterexample (C ε₀ : ℝ) (hC : 0 ≤ C) (hε : 0 < ε₀) :
    NuclearTransferFailure C ε₀ := by
  sorry

end NLA.RA08.Paper
end
end
