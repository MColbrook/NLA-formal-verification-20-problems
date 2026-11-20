module

public import Mathlib

@[expose] public section

/-!
Standalone statement surface for MI-19.
Definitions and selected theorem types are retained from the original sources.
Historical notices below are preserved; current review status is in the audit records.
-/


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.MI19.Definitions -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-19.
This file is the proof-independent statement boundary. No local theorem is imported.
-/





set_option autoImplicit false

open scoped BigOperators ComplexOrder
noncomputable section

namespace NLA.MI19

/-- The number of inversions in the full original ordering of `Fin n`.
The paper's index `i + 1` is represented by Lean index `i`. -/
def inversionCount {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    fun ij => ij.1 < ij.2 ∧ σ ij.2 < σ ij.1).card

/-- The term of the complex `q`-permanent belonging to a permutation.
The natural power retains the convention `0 ^ 0 = 1`. -/
def qPermanentTerm {n : ℕ} (q : ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
    (σ : Equiv.Perm (Fin n)) : ℂ :=
  (q : ℂ) ^ inversionCount σ * ∏ i : Fin n, A i (σ i)

/-- The `q`-permanent, with all inversions counted in the original ordering. -/
def qPermanent {n : ℕ} (q : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ σ : Equiv.Perm (Fin n), qPermanentTerm q A σ

/-- Setwise preservation, not pointwise fixation and not an initial-segment test. -/
abbrev PreservesSubset {n : ℕ} (σ : Equiv.Perm (Fin n)) (S : Finset (Fin n)) : Prop :=
  S.image σ = S

/-- The subset-preserving sum. The exponent still uses `inversionCount` on
all `n` positions; it is not a product of smaller `q`-permanents. -/
def restrictedQPermanent {n : ℕ} (q : ℝ) (A : Matrix (Fin n) (Fin n) ℂ)
    (S : Finset (Fin n)) : ℂ :=
  ∑ σ ∈ (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
    (fun σ => PreservesSubset σ S), qPermanentTerm q A σ

/-- The full canonical MI-19 conjecture, over complex Hermitian PSD matrices
and every nonempty proper subset. `ComplexOrder` compares real parts and requires
equal imaginary parts; on real-valued expressions this is exactly real order. -/
def SubsetConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef →
    ∀ q : ℝ, 0 ≤ q → q ≤ 1 → ∀ S : Finset (Fin n),
      S.Nonempty → S ≠ Finset.univ → restrictedQPermanent q A S ≤ qPermanent q A

/-- Colbrook's exact real Gram witness, viewed as a complex matrix. -/
def witness : Matrix (Fin 4) (Fin 4) ℂ :=
  !![170, 1, 167, 170; 1, 1, -2, 1; 167, -2, 173, 167; 170, 1, 167, 170]

/-- The rectangular Gram factor, to be proved to satisfy `Xᴴ * X = witness`. -/
def gramFactor : Matrix (Fin 2) (Fin 4) ℂ :=
  !![13, 0, 13, 13; 1, 1, -2, 1]

/-- The parameter lies strictly between the two allowed endpoints. -/
def witnessQ : ℝ := 7 / 8

/-- The interior singleton `{2}` in the paper's one-based indexing. -/
def witnessSubset : Finset (Fin 4) := {1}

end NLA.MI19
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.MI19.PaperDefinitions -/



set_option autoImplicit false
noncomputable section
namespace NLA.MI19.Paper

def realWitness : Matrix (Fin 4) (Fin 4) ℝ :=
  !![170,1,167,170; 1,1,-2,1; 167,-2,173,167; 170,1,167,170]

end NLA.MI19.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: PaperChallenge -/


set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace NLA.MI19.Paper

theorem paper_counterexample :
    realWitness.PosSemidef ∧ realWitness.rank = 2 ∧
    witness = realWitness.map (fun x : ℝ => (x : ℂ)) ∧
    0 ≤ witnessQ ∧ witnessQ ≤ 1 ∧
    witnessSubset.Nonempty ∧ witnessSubset ≠ Finset.univ ∧
    qPermanent witnessQ witness - restrictedQPermanent witnessQ witness witnessSubset =
      (-3235575 / 16384 : ℂ) ∧
    qPermanent witnessQ witness < restrictedQPermanent witnessQ witness witnessSubset := by
  sorry

end NLA.MI19.Paper
end
end
