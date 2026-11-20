module

public import Mathlib

@[expose] public section

/-!
Standalone statement surface for RA-02, RA-03.
Definitions and selected theorem types are retained from the original sources.
Historical notices below are preserved; current review status is in the audit records.
-/


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.Definitions -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted statement draft.
Original mathematical resolution: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge.

Definitions only. No normalization, PSD preservation, spectral estimate,
history identity, or counterexample bound is assumed here. All are independent
Challenge obligations. The finite arrowhead route is an alternative to the
retained manuscript's stronger sharp limiting construction.
-/





set_option autoImplicit false

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev History (n k : ℕ) := Fin k → Fin n

def realTrace {n : ℕ} (A : Square n) : ℝ := A.trace.re

def quadraticValue {n : ℕ} (A : Square n) (x : Fin n → ℂ) : ℝ :=
  (star x ⬝ᵥ (A *ᵥ x)).re

/-- Actual squared Euclidean norm, with no entrywise max norm. -/
def squaredNorm {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

/-- Zero-diagonal choices are harmless totalization. Their probability is zero
for a nonzero PSD residual. The nonzero case is the original complex update. -/
def choleskyStep {n : ℕ} (A : Square n) (j : Fin n) : Square n :=
  if A j j = 0 then A else fun a b => A a b - A a j * A j b / A j j

/-- On a zero PSD residual use uniform dummy labels; all residuals stay zero.
The n=0 value is only totalization: normalization is asserted for n>=1. -/
def pivotMass {n : ℕ} (A : Square n) (j : Fin n) : ℝ :=
  if realTrace A = 0 then 1 / (n : ℝ) else (A j j).re / realTrace A

/-- Chronological residual, including all zero-probability paths. -/
def pathResidual {n : ℕ} (A : Square n) : List (Fin n) → Square n
  | [] => A
  | j :: w => pathResidual (choleskyStep A j) w

/-- Product of actual conditional masses; no independence assumption. -/
def pathWeight {n : ℕ} (A : Square n) : List (Fin n) → ℝ
  | [] => 1
  | j :: w => pivotMass A j * pathWeight (choleskyStep A j) w

def pathContribution {n : ℕ} (A : Square n) (w : List (Fin n)) : ℝ :=
  pathWeight A w * realTrace (pathResidual A w)

/-- Full finite expectation. Every ordered label sequence is included. -/
def expectedTrace {n : ℕ} (A : Square n) (k : ℕ) : ℝ :=
  ∑ f : History n k, pathContribution A (List.ofFn f)

/-- Mathlib's genuinely decreasing eigenvalues. The finite-index transport
uses only card(Fin n)=n; the separately reindexed eigenvalues is not used. -/
def orderedEigenvalues {n : ℕ} (A : Square n) (hA : A.IsHermitian) : Fin n → ℝ :=
  fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

/-- Zero-based i>=r is the original one-based j>r tail. -/
def rankTail {n : ℕ} (A : Square n) (hA : A.IsHermitian) (r : ℕ) : ℝ :=
  ∑ i ∈ (Finset.univ.filter fun i : Fin n => r ≤ i.val), orderedEigenvalues A hA i

/-- The complete positive assertion in the original RA-02 question. -/
def PolynomialTraceFactor : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p : ℝ, 0 ≤ p ∧
    ∀ n : ℕ, 1 ≤ n → ∀ A : Square n, ∀ hA : A.PosSemidef,
      ∀ r : ℕ, 1 ≤ r → r ≤ n →
        expectedTrace A r ≤ C * Real.rpow (r : ℝ) p * rankTail A hA.isHermitian r

/-- Exact parameters, never machine-floating-point constants. -/
def smallParameter (r : ℕ) : ℝ := 1 / (2 * (r : ℝ) + 1)
def scaleParameter (r : ℕ) : ℝ := smallParameter r ^ (2 * (r + 1))
def diagonalWeight (r i : ℕ) : ℝ := scaleParameter r ^ i
def couplingWeight (r i : ℕ) : ℝ := smallParameter r ^ (i + 1)

def cornerValue (r : ℕ) (U : Finset (Fin r)) : ℝ :=
  scaleParameter r ^ r + ∑ i ∈ U, diagonalWeight r i.val * couplingWeight r i.val ^ 2

def ordinaryLabels {r : ℕ} (U : Finset (Fin r)) : Finset (Fin (r + 1)) :=
  U.image (fun i : Fin r => i.castSucc)

/-- The two explicit residual shapes, zero-padded in the original label set.
`lastPresent=true` means the distinguished pivot has not been selected. -/
def arrowheadState (r : ℕ) (U : Finset (Fin r)) (lastPresent : Bool) : Square (r + 1) :=
  fun i j =>
    if i ∈ ordinaryLabels U ∧ j ∈ ordinaryLabels U then
      (((if i = j then diagonalWeight r i.val else 0) -
        (if lastPresent then 0 else
          (diagonalWeight r i.val * couplingWeight r i.val) *
            (diagonalWeight r j.val * couplingWeight r j.val) / cornerValue r U)) : ℝ)
    else if lastPresent then
      if i = Fin.last r ∧ j = Fin.last r then (cornerValue r U : ℂ)
      else if i = Fin.last r ∧ j ∈ ordinaryLabels U then
        ((diagonalWeight r j.val * couplingWeight r j.val : ℝ) : ℂ)
      else if j = Fin.last r ∧ i ∈ ordinaryLabels U then
        ((diagonalWeight r i.val * couplingWeight r i.val : ℝ) : ℂ)
      else 0
    else 0

/-- The explicit real-entry complex witness of order r+1. -/
def arrowhead (r : ℕ) : Square (r + 1) := arrowheadState r Finset.univ true

def rayleighProbe (r : ℕ) (i : Fin (r + 1)) : ℂ :=
  if i = Fin.last r then 1 else (-(couplingWeight r i.val) : ℝ)

def remainingOrdinary (r : ℕ) (w : List (Fin (r + 1))) : Finset (Fin r) :=
  Finset.univ.filter fun i => i.castSucc ∉ w

def lastRemaining (r : ℕ) (w : List (Fin (r + 1))) : Bool :=
  !(w.contains (Fin.last r))

/-- Actual chronological prefix traces, including the initial trace. -/
def prefixTraceProduct {n : ℕ} (A : Square n) (w : List (Fin n)) : ℝ :=
  ∏ s : Fin w.length, realTrace (pathResidual A (w.take s.val))

/-- Actual pivot values, with the label at that position read from the list. -/
def pivotProduct {n : ℕ} (A : Square n) (w : List (Fin n)) : ℝ :=
  ∏ s : Fin w.length, ((pathResidual A (w.take s.val)) (w.get s) (w.get s)).re

def commonNumerator (r : ℕ) : ℝ :=
  scaleParameter r ^ r * ∏ i : Fin r, diagonalWeight r i.val

/-- At stage s<r, true chooses the carried label and replaces it by s.
The extension past r is totalization only and is not used in the proof. -/
def carryLabel (r : ℕ) (bits : Fin r → Bool) : ℕ → Fin (r + 1)
  | 0 => Fin.last r
  | s + 1 => if hs : s < r then
      if bits ⟨s, hs⟩ then (⟨s, hs⟩ : Fin r).castSucc else carryLabel r bits s
    else carryLabel r bits s

def retainedHistory (r : ℕ) (bits : Fin r → Bool) : History (r + 1) r :=
  fun s => if bits s then carryLabel r bits s.val else s.castSucc

/-- The full set of binary-encoded histories, not the process's sample space. -/
def retainedHistories (r : ℕ) : Finset (History (r + 1) r) :=
  Finset.univ.image (retainedHistory r)

def retainedPrefix (r : ℕ) (bits : Fin r → Bool) (s : ℕ) : List (Fin (r + 1)) :=
  (List.ofFn (retainedHistory r bits)).take s

def initialLabels (r s : ℕ) : Finset (Fin (r + 1)) :=
  Finset.univ.filter fun j => j.val < s ∨ j = Fin.last r

end
end NLA.RA02
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA03.Definitions -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to RA-03.
This file is the proof-independent statement boundary. No local theorem is imported.
-/






set_option autoImplicit false

open scoped BigOperators Classical
noncomputable section

namespace NLA.RA03

/-- The squared Frobenius norm, written as the exact sum of squared complex moduli. -/
def frobeniusSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- `none` is the absorbing label used only after the residual is zero.
Each `some (i,j)` selects a row and a column together. -/
abbrev Pivot (m n : ℕ) := Option (Fin m × Fin n)

/-- The exact conditional pivot probabilities. The zero residual assigns
probability one to `none`; otherwise only entry labels have nonzero mass. -/
def pivotMass {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) : Pivot m n → ℝ
  | none => if S = 0 then 1 else 0
  | some ij => if S = 0 then 0 else Complex.normSq (S ij.1 ij.2) / frobeniusSq S

/-- The canonical rank-one cross update. A zero entry is given an identity
update solely to totalize the function; its selection probability is zero. -/
def pivotResidual {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ)
    (ij : Fin m × Fin n) : Matrix (Fin m) (Fin n) ℂ :=
  if S ij.1 ij.2 = 0 then S
  else fun a b => S a b - S a ij.2 * S ij.1 b / S ij.1 ij.2

/-- The next residual for a transition label. The `none` transition has
positive mass exactly at the zero matrix, where it keeps the residual zero. -/
def nextResidual {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) :
    Pivot m n → Matrix (Fin m) (Fin n) ℂ
  | none => 0
  | some ij => pivotResidual S ij

/-- The terminal residual along an ordered history of `k` transitions. -/
def historyResidual {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) :
    {k : ℕ} → (Fin k → Pivot m n) → Matrix (Fin m) (Fin n) ℂ
  | 0, _ => S
  | k + 1, h => historyResidual (nextResidual S (h 0)) (fun i : Fin k => h i.succ)

/-- The joint probability of a history is the product of the conditional
probabilities along its actual residuals. No independence of row and column
choices, or of successive pivot choices, is assumed. -/
def historyMass {m n : ℕ} (S : Matrix (Fin m) (Fin n) ℂ) :
    {k : ℕ} → (Fin k → Pivot m n) → ℝ
  | 0, _ => 1
  | k + 1, h => pivotMass S (h 0) *
      historyMass (nextResidual S (h 0)) (fun i : Fin k => h i.succ)

/-- The actual finite expectation after exactly `k` transitions. Absorption
implements the canonical instruction to keep all later residuals zero. -/
def expectedError {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) : ℝ :=
  ∑ h : Fin k → Pivot m n, historyMass A h * frobeniusSq (historyResidual A h)

/-- The decreasing singular values of the matrix acting on complex Euclidean
spaces, using mathlib's zero-based sequence with its actual spectral definition. -/
def singularValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (j : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues j

/-- The canonical squared singular-value tail after rank `k`.
Paper indices `j > k` become zero-based indices in `[k, min m n)`. -/
def singularTailSq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ico k (min m n), singularValue A j ^ 2

/-- The full original RA-03 assertion: arbitrary rectangular complex inputs,
all positive dimensions, and every admissible number of pivots. -/
def SquaredErrorConjecture : Prop :=
  ∀ m n : ℕ, 1 ≤ m → 1 ≤ n → ∀ A : Matrix (Fin m) (Fin n) ℂ,
    ∀ k : ℕ, 1 ≤ k → k ≤ min m n →
      expectedError A k ≤ (2 : ℝ) ^ k * singularTailSq A k

/-- Colbrook's exact real order-two witness, regarded as a complex matrix. -/
def witness : Matrix (Fin 2) (Fin 2) ℂ := !![2, 1; 1, 2]

/-- The candidate Gram matrix; equality with `witnessᴴ * witness` is a proof obligation. -/
def witnessGram : Matrix (Fin 2) (Fin 2) ℂ := !![5, 4; 4, 5]

/-- The four exact pivot probabilities, to be derived from `pivotMass`. -/
def witnessPivotMass : Matrix (Fin 2) (Fin 2) ℝ := !![2 / 5, 1 / 10; 1 / 10, 2 / 5]

/-- The four squared residual errors, to be derived from `pivotResidual`. -/
def witnessPivotError : Matrix (Fin 2) (Fin 2) ℝ := !![9 / 4, 9; 9, 9 / 4]

end NLA.RA03
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.PaperLUUpperDefinitions -/



set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper

/-- The actual ordered-eigenvalue tail of the complex Gram matrix. -/
def gramTail {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) : ℝ :=
  NLA.RA02.rankTail (A.conjTranspose*A) (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian r

end NLA.RA02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.PaperRectangularBestDefinitions -/



set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- Infimum of actual squared Frobenius errors over complex rectangular
matrices of rank at most r. No spectral approximation theorem is assumed. -/
def rectangularBestRankErrorSquared {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ B : Matrix (Fin m) (Fin n) ℂ, B.rank ≤ r ∧ NLA.RA03.frobeniusSq (A-B) = e}

end NLA.RA02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.PaperLUSupDefinitions -/


set_option autoImplicit false
noncomputable section
open scoped ComplexOrder
namespace NLA.RA02.Paper

/-- Actual LU ratios over all complex rectangular matrix inputs with positive
best rank-r squared Frobenius error. No dimension or nonsingularity condition. -/
def luRatios (r : ℕ) : Set ℝ :=
  {x | ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ),
    0 < rectangularBestRankErrorSquared A r ∧
    x = NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r}

/-- The same ratios restricted to real positive-definite, entrywise-positive inputs. -/
def realPositiveLURatios (r : ℕ) : Set ℝ :=
  {x | ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosDef),
    (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧
    0 < rectangularBestRankErrorSquared A r ∧
    x = NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r}

end NLA.RA02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.PaperCholeskySupDefinitions -/


set_option autoImplicit false
noncomputable section
open scoped ComplexOrder
namespace NLA.RA02.Paper

/-- Ratios for arbitrary complex PSD inputs with a positive rank-r tail. -/
def choleskyRatios (r : ℕ) : Set ℝ :=
  {x | ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosSemidef), r ≤ n ∧
    0 < NLA.RA02.rankTail A hA.isHermitian r ∧
    x = NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r}

/-- Restriction to real, positive-definite, entrywise-positive inputs. -/
def realPositiveCholeskyRatios (r : ℕ) : Set ℝ :=
  {x | ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosDef),
    (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧ r ≤ n ∧
    0 < NLA.RA02.rankTail A hA.isHermitian r ∧
    x = NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r}

end NLA.RA02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.PaperSharpDefinitions -/



set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- The printed lower-triangular factor, with paper indices shifted by one. -/
def lower (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i = j then 1 else if j < i then t^(j.val+1) / (i.val+j.val+2 : ℕ) else 0

def epsilon (n : ℕ) (t : ℝ) : ℝ := t^(n^2)

def diagonalScales (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => epsilon n t ^ i.val)

/-- The exact L(t) D(t) L(t)^T family in the manuscript, in size n=r+1. -/
def sharpFamily (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  lower n t * diagonalScales n t * (lower n t).transpose

def prefixMatrix {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Matrix (Fin s) (Fin s) ℝ := (lower n t).submatrix rows (Fin.castLE hs)

def prefixDegree {n s : ℕ} (hs : s ≤ n) (rows : Fin s ↪ Fin n) : ℕ :=
  ∑ j : Fin s, if Fin.castLE hs j ∈ Set.range rows then 0 else j.val+1

end NLA.RA02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.PaperInterpolationDefinitions -/


set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace NLA.RA02.Paper

def nextColumn {n s : ℕ} (hs : s < n) (t : ℝ) : Fin n → ℝ :=
  fun i => lower n t i ⟨s,hs⟩

def interpolationCoefficients {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Fin s → ℝ := (prefixMatrix hs.le rows t)⁻¹ *ᵥ (fun i => nextColumn hs t (rows i))

def interpolationResidual {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Fin n → ℝ := nextColumn hs t -
      ((lower n t).submatrix id (Fin.castLE hs.le)) *ᵥ interpolationCoefficients hs rows t

def interpolationSquaredNorm {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) : ℝ :=
  ∑ i : Fin n, (interpolationResidual hs rows t i)^2

end NLA.RA02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.PaperResidualDefinitions -/


set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.RA02.Paper

def interpolatoryResidual {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin s ↪ Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  A - A.submatrix id cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id

def paperTrace {n s : ℕ} (rows : Fin s ↪ Fin n) (t : ℝ) : ℝ :=
  (interpolatoryResidual (sharpFamily n t) rows rows).trace

def paperFrobeniusSquared {n s : ℕ} (rows cols : Fin s ↪ Fin n) (t : ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, (interpolatoryResidual (sharpFamily n t) rows cols i j)^2

end NLA.RA02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.PaperPivotDefinitions -/


set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- The real rank-one pivot update. Division by zero leaves the matrix unchanged. -/
def crossUpdate {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i j - A i q * A p j / A p q

def complexify {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (A i j : ℂ)

def realCholeskyPath {n : ℕ} : Matrix (Fin n) (Fin n) ℝ → List (Fin n) → Matrix (Fin n) (Fin n) ℝ
  | A, [] => A
  | A, j :: w => realCholeskyPath (crossUpdate A j j) w

def realLUNext {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Option (Fin n × Fin n) → Matrix (Fin n) (Fin n) ℝ
  | none => 0
  | some ij => crossUpdate A ij.1 ij.2

def realLUPath {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    {k : ℕ} → (Fin k → Option (Fin n × Fin n)) → Matrix (Fin n) (Fin n) ℝ
  | 0, _ => A
  | k+1, h => realLUPath (realLUNext A (h 0)) (fun i : Fin k => h i.succ)

def realLUListPath {n : ℕ} : Matrix (Fin n) (Fin n) ℝ → List (Option (Fin n × Fin n)) → Matrix (Fin n) (Fin n) ℝ
  | A, [] => A
  | A, p :: w => realLUListPath (realLUNext A p) w

end NLA.RA02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.PaperTailDefinitions -/



set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- Actual ordered-eigenvalue tail of the printed family, totalized away from
Hermitian inputs. The family is proved Hermitian whenever t is positive. -/
def familyRankTail (r : ℕ) (t : ℝ) : ℝ :=
  if h : (complexify (sharpFamily (r+1) t)).IsHermitian then
    NLA.RA02.rankTail (complexify (sharpFamily (r+1) t)) h r else 0

/-- Actual squared singular-value tail used by the archived LU algorithm. -/
def familySingularTailSquared (r : ℕ) (t : ℝ) : ℝ :=
  NLA.RA03.singularTailSq (complexify (sharpFamily (r+1) t)) r

end NLA.RA02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.PaperBestErrorDefinitions -/



set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- Infimum of actual squared Frobenius errors over all complex matrices of
rank at most r. Attainment and its spectral value are proved separately. -/
def bestRankErrorSquared {n : ℕ} (A : NLA.RA02.Square n) (r : ℕ) : ℝ :=
  sInf {e : ℝ | ∃ B : NLA.RA02.Square n, B.rank ≤ r ∧ NLA.RA03.frobeniusSq (A-B) = e}

end NLA.RA02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA02.LUSupChallenge -/




set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem paper_sup_worst_case_constants (r : ℕ) :
    IsLUB (choleskyRatios r) ((2:ℝ)^r) ∧ IsLUB (realPositiveCholeskyRatios r) ((2:ℝ)^r) ∧ IsLUB (luRatios r) ((4:ℝ)^r) ∧ IsLUB (realPositiveLURatios r) ((4:ℝ)^r) := by
  sorry

end NLA.RA02.Paper
end
end
