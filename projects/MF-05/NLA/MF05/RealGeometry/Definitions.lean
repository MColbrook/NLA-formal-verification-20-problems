module

/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted statement draft.
Original mathematical proof: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge.

Definitions only. No bound, norm existence, limit, or correspondence theorem is
assumed. The independent Challenge contains the complete proof obligations.
-/
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.List.OfFn
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

set_option autoImplicit false

namespace NLA.MF05.RealGeometry
noncomputable section

abbrev Square (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev EuclideanVector (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Actual real Euclidean operator norm, with no default entrywise norm. -/
def spectralNorm {d : ℕ} (A : Square d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖

def applyMatrix {d : ℕ} (A : Square d) (x : EuclideanVector d) : EuclideanVector d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x

/-- Chronological order: later factors act on the left. -/
def matrixProduct {d : ℕ} (w : List (Square d)) : Square d := w.reverse.prod

def finiteProduct {d n : ℕ} (A : Fin n → Square d) : Square d :=
  matrixProduct (List.ofFn A)

def WordIn {d : ℕ} (M : Set (Square d)) (w : List (Square d)) : Prop :=
  ∀ A ∈ w, A ∈ M

/-- The actual supremum; compact attainment is an independent obligation. -/
def familyNorm {d : ℕ} (M : Set (Square d)) : ℝ := sSup (spectralNorm '' M)

/-- All words are retained, including repetitions and infinitely many possible
generators. This is not a finite-generator restriction. -/
def wordNorms {d : ℕ} (M : Set (Square d)) (n : ℕ) : Set ℝ :=
  {r | ∃ w : List (Square d), w.length = n ∧ WordIn M w ∧
    r = spectralNorm (matrixProduct w)}

def familyGrowth {d : ℕ} (M : Set (Square d)) (n : ℕ) : ℝ := sSup (wordNorms M n)

/-- The n=0 value is immaterial to the limit and excluded from the infimum. -/
def rootGrowth {d : ℕ} (M : Set (Square d)) (n : ℕ) : ℝ :=
  Real.rpow (familyGrowth M n) (1 / (n : ℝ))

/-- Fekete's infimum formula. Its radius-one equivalence with the canonical
root limit is mandatory; no radius is assigned by definition. -/
def jointSpectralRadius {d : ℕ} (M : Set (Square d)) : ℝ :=
  sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = rootGrowth M n}

/-- Ordinary real norm axioms, without a product-bound assumption. -/
def IsNorm {d : ℕ} (v : EuclideanVector d → ℝ) : Prop :=
  (∀ x, 0 ≤ v x) ∧ (∀ x, v x = 0 ↔ x = 0) ∧
  (∀ x y, v (x + y) ≤ v x + v y) ∧
  (∀ c : ℝ, ∀ x, v (c • x) = ‖c‖ * v x)

def IsUnitary {d : ℕ} (Q : Square d) : Prop :=
  Q.conjTranspose * Q = 1 ∧ Q * Q.conjTranspose = 1

def diagonalWeights {d : ℕ} (σ : Fin d → ℝ) : Square d :=
  Matrix.diagonal (fun i => (σ i : ℝ))

def inverseDiagonalWeights {d : ℕ} (σ : Fin d → ℝ) : Square d :=
  Matrix.diagonal (fun i => ((σ i)⁻¹ : ℝ))

def rotatedGenerator {d : ℕ} (Q : Square d) (σ : Fin d → ℝ) (A : Square d) :
    Square d := inverseDiagonalWeights σ * Q.conjTranspose * A * Q * diagonalWeights σ

/-- Full diagonal blocks with equal weight are allowed. Only entries strictly
above the weight blocks must vanish. -/
def LowerForWeights {d : ℕ} (h : Fin d → ℝ) (X : Square d) : Prop :=
  ∀ i j : Fin d, h j < h i → X i j = 0

def diagonalDamping {d : ℕ} (h : Fin d → ℝ) (X : Square d) : Square d :=
  diagonalWeights h * X * inverseDiagonalWeights h


end
end NLA.MF05.RealGeometry
