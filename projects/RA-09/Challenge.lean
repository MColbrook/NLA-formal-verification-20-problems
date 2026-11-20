module

public import Mathlib

@[expose] public section

/-!
Standalone statement surface for RA-09.
Definitions and selected theorem types are retained from the original sources.
Historical notices below are preserved; current review status is in the audit records.
-/


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA09.Definitions -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical theorem: Matthew J. Colbrook. Original question: Persson–Meyer–Musco.
Spectral-data/CFC design adapted from the campaign's proof-independent RA08
statement definitions; no RA08 implementation or admitted theorem is imported.
-/








set_option autoImplicit false
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.RA09

abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- Finite real entry squares; equality with actual Frobenius norm squared is an obligation. -/
def frobeniusSquared {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

section FrobeniusInstance
open scoped Matrix.Norms.Frobenius
/-- The actual Mathlib Frobenius norm, with its instance isolated from CFC. -/
def frobeniusNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := ‖A‖
end FrobeniusInstance

/-- Exactly the canonical half-line function class, with arbitrary extension below zero. -/
def AdmissibleFunction (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) f ∧
    MonotoneOn f (Set.Ici 0) ∧ ∀ x : ℝ, 0 ≤ x → 0 ≤ f x

/-- Every allowed ordered orthonormal decomposition of the actual matrix. -/
structure OrderedSpectralData {n : ℕ} (A : RealMatrix n) where
  eigenvalues : Fin n → ℝ
  orthogonal : Matrix.unitaryGroup (Fin n) ℝ
  decreasing : Antitone eigenvalues
  nonnegative : ∀ i, 0 ≤ eigenvalues i
  reconstruct : A =
    (orthogonal : RealMatrix n) * Matrix.diagonal eigenvalues *
      (orthogonal : RealMatrix n).transpose

def spectralCombination {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (values : Fin n → ℝ) : RealMatrix n :=
  (d.orthogonal : RealMatrix n) * Matrix.diagonal values *
    (d.orthogonal : RealMatrix n).transpose

def truncation {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) : RealMatrix n :=
  spectralCombination d (fun i => if i.val < k then d.eigenvalues i else 0)

/-- Genuine Mathlib real functional calculus, not a stipulated spectral formula. -/
def functionalCalculus {n : ℕ} (f : ℝ → ℝ) (A : RealMatrix n) : RealMatrix n :=
  cfc (R := ℝ) f A

/-- SAME basis as the original truncation; discarded entries stay zero even when f(0)>0. -/
def functionTruncation {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (k : ℕ) : RealMatrix n :=
  spectralCombination d (fun i => if i.val < k then f (d.eigenvalues i) else 0)

def spectralTail {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), d.eigenvalues i ^ 2

def functionTail {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), f (d.eigenvalues i) ^ 2

def overlapMatrix {n : ℕ} {A Ahat : RealMatrix n}
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat) : RealMatrix n :=
  (dA.orthogonal : RealMatrix n).transpose * (dHat.orthogonal : RealMatrix n)

def overlapWeights {n : ℕ} {A Ahat : RealMatrix n}
    (dA : OrderedSpectralData A) (dHat : OrderedSpectralData Ahat) : RealMatrix n :=
  fun i j => overlapMatrix dA dHat i j ^ 2

/-- The actual rank-one real outer product. -/
def outerSquare {n : ℕ} (v : Fin n → ℝ) : RealMatrix n := fun i j => v i * v j

def transferScale (f : ℝ → ℝ) (τ : ℝ) : ℝ := f τ / τ
def scalarAuxiliary (f : ℝ → ℝ) (τ a : ℝ) : ℝ :=
  max ((transferScale f τ)^2 * a^2 - (f a)^2) 0
def branchQuadratic (d z : ℝ) : ℝ := 2*(d+1)*z^2 - (2*d+1)*z + d

/-- Complete original assertion: the premise is the difference of squared norms,
not a substituted residual premise. Every permitted eigenbasis is quantified. -/
def ConcaveFrobeniusTransferConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k → k < n →
    ∀ A Ahat : RealMatrix n, A.PosSemidef → Ahat.PosSemidef → Ahat ≤ A →
      ∀ f : ℝ → ℝ, AdmissibleFunction f →
        ∀ dA : OrderedSpectralData A, ∀ dHat : OrderedSpectralData Ahat,
          ∀ ε : ℝ, 0 ≤ ε →
            frobeniusSquared A - frobeniusSquared (truncation dHat k) ≤
                (1+ε) * frobeniusSquared (A - truncation dA k) →
            frobeniusSquared (functionalCalculus f A - functionTruncation dHat f k) ≤
                (1+ε) * frobeniusSquared (functionalCalculus f A - functionTruncation dA f k)

end NLA.RA09
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA09.PaperDefinitions -/


/- The larger function class in main.tex, equation raf-eq:subhom.
No concavity assumption is part of this paper-specific definition. -/
namespace NLA.RA09

def PaperAdmissibleFunction (f : ℝ → ℝ) : Prop :=
  ContinuousOn f (Set.Ici 0) ∧ MonotoneOn f (Set.Ici 0) ∧
    (∀ x : ℝ, 0 ≤ x → 0 ≤ f x) ∧
    ∀ x y : ℝ, 0 < x → x ≤ y → f y / y ≤ f x / x

end NLA.RA09
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA09.PaperSharpnessDefinitions -/


/-! Independent sharpness specification in actual matrix quantities. -/
noncomputable section
namespace NLA.RA09

def UnorderedSharpnessWitness (γ : ℝ) : Prop :=
  ∃ (n : ℕ) (hn : 1 < n) (p : ℝ) (A B : RealMatrix n)
      (dA : OrderedSpectralData A) (dB : OrderedSpectralData B),
    0 < p ∧ p < 1 ∧ B.rank ≤ 1 ∧ dA.eigenvalues ⟨1,hn⟩ = 1 ∧
    0 < spectralTail dA 1 ∧
    0 < frobeniusSquared (A-B) - spectralTail dA 1 ∧
    0 < frobeniusNorm (A-B) / Real.sqrt (spectralTail dA 1) - 1 ∧
    γ * (frobeniusSquared (A-B) - spectralTail dA 1) <
      frobeniusSquared (functionalCalculus (fun x : ℝ => x^p) A -
        functionTruncation dB (fun x : ℝ => x^p) 1) -
      functionTail dA (fun x : ℝ => x^p) 1 ∧
    γ * (frobeniusNorm (A-B) / Real.sqrt (spectralTail dA 1) - 1) <
      frobeniusNorm (functionalCalculus (fun x : ℝ => x^p) A -
        functionTruncation dB (fun x : ℝ => x^p) 1) /
          Real.sqrt (functionTail dA (fun x : ℝ => x^p) 1) - 1

end NLA.RA09
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.RA09.PaperHarmonicDefinitions -/


/-! Independent matrix specification for the Moore–Penrose harmonic lemma. -/
noncomputable section
namespace NLA.RA09

def spectralPseudoinverse {n : ℕ} (A : RealMatrix n) : RealMatrix n :=
  functionalCalculus (fun x : ℝ => x⁻¹) A

def IsMoorePenroseInverse {n : ℕ} (A P : RealMatrix n) : Prop :=
  A*P*A = A ∧ P*A*P = P ∧ (A*P).IsHermitian ∧ (P*A).IsHermitian

end NLA.RA09
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: PaperChallenge -/






/- Independent statements for the paper. Deliberate challenge holes are not proof dependencies. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix
namespace NLA.RA09

theorem paper_ordered_matrix_norm_relative {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (hBA : B ≤ A) (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hA : frobeniusNorm (A-B) ≤ (1+ε)*Real.sqrt (spectralTail dA k)) :
    frobeniusNorm (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+ε)*Real.sqrt (functionTail dA f k) := by
  sorry

theorem paper_unordered_matrix_norm_relative {n : ℕ} {A B : RealMatrix n}
    (dA : OrderedSpectralData A) (dB : OrderedSpectralData B)
    (f : ℝ → ℝ) (hf : PaperAdmissibleFunction f)
    (k : ℕ) (hk : k < n) (hB : B.rank ≤ k) (hτ : 0 < dA.eigenvalues ⟨k,hk⟩)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hA : frobeniusNorm (A-B) ≤ (1+ε)*Real.sqrt (spectralTail dA k)) :
    frobeniusNorm (functionalCalculus f A - functionTruncation dB f k) ≤
      (1+2*ε)*Real.sqrt (functionTail dA f k) := by
  sorry

theorem paper_ordered_sharpness (γ : ℝ) (hγ : γ < 1) :
    ∃ (A B : RealMatrix 3) (dA : OrderedSpectralData A) (dB : OrderedSpectralData B),
      B ≤ A ∧ B.rank ≤ 1 ∧ dA.eigenvalues ⟨1, by decide⟩ = 1 ∧
      frobeniusSquared (A-B) - spectralTail dA 1 = 1 ∧
      γ * (frobeniusSquared (A-B) - spectralTail dA 1) <
        frobeniusSquared (functionalCalculus (fun x : ℝ => x) A -
          functionTruncation dB (fun x : ℝ => x) 1) - functionTail dA (fun x : ℝ => x) 1 := by
  sorry

theorem paper_unordered_sharpness (γ : ℝ) (hγ : γ < 2) : UnorderedSharpnessWitness γ := by
  sorry

end NLA.RA09
end
end
