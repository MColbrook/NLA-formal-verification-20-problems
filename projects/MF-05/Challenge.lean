module

public import Mathlib

@[expose] public section

/-!
Standalone statement surface for MF-05, MF-07.
Definitions and selected theorem types are retained from the original sources.
Historical notices below are preserved; current review status is in the audit records.
-/


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.MF07.Definitions -/
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







set_option autoImplicit false

namespace NLA.MF07
noncomputable section

abbrev Square (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev EuclideanVector (d : ℕ) := EuclideanSpace ℂ (Fin d)

/-- Actual complex Euclidean operator norm, with no default entrywise norm. -/
def spectralNorm {d : ℕ} (A : Square d) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A‖

def applyMatrix {d : ℕ} (A : Square d) (x : EuclideanVector d) : EuclideanVector d :=
  Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A x

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

/-- Ordinary complex norm axioms, without a product-bound assumption. -/
def IsComplexNorm {d : ℕ} (v : EuclideanVector d → ℝ) : Prop :=
  (∀ x, 0 ≤ v x) ∧ (∀ x, v x = 0 ↔ x = 0) ∧
  (∀ x y, v (x + y) ≤ v x + v y) ∧
  (∀ c : ℂ, ∀ x, v (c • x) = ‖c‖ * v x)

def IsUnitary {d : ℕ} (Q : Square d) : Prop :=
  Q.conjTranspose * Q = 1 ∧ Q * Q.conjTranspose = 1

def diagonalWeights {d : ℕ} (σ : Fin d → ℝ) : Square d :=
  Matrix.diagonal (fun i => (σ i : ℂ))

def inverseDiagonalWeights {d : ℕ} (σ : Fin d → ℝ) : Square d :=
  Matrix.diagonal (fun i => ((σ i)⁻¹ : ℂ))

def rotatedGenerator {d : ℕ} (Q : Square d) (σ : Fin d → ℝ) (A : Square d) :
    Square d := inverseDiagonalWeights σ * Q.conjTranspose * A * Q * diagonalWeights σ

/-- Full diagonal blocks with equal weight are allowed. Only entries strictly
above the weight blocks must vanish. -/
def LowerForWeights {d : ℕ} (h : Fin d → ℝ) (X : Square d) : Prop :=
  ∀ i j : Fin d, h j < h i → X i j = 0

def diagonalDamping {d : ℕ} (h : Fin d → ℝ) (X : Square d) : Square d :=
  diagonalWeights h * X * inverseDiagonalWeights h

/-- A rational dimension-only enlargement of the source's explicit constant.
The value at zero is a total-definition convenience; the target has d ≥ 1. -/
def growthConstant (d : ℕ) : ℝ :=
  if d ≤ 1 then 1 else
    (d : ℝ) * (6 * (d : ℝ) ^ 2 / ((d - 1 : ℕ) : ℝ)) ^ (d - 1)

def comparisonThreshold (d n : ℕ) (L : ℝ) : ℝ :=
  2 * (d : ℝ) ^ 2 * L * (n : ℝ) / ((d - 1 : ℕ) : ℝ)

end
end NLA.MF07
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.MF07.MatrixBasics -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical argument:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge.
-/





set_option autoImplicit false


noncomputable section
namespace NLA.MF07

@[simp] lemma matrixProduct_nil {d : ℕ} : matrixProduct ([] : List (Square d)) = 1 := by
  simp [matrixProduct]

@[simp] lemma matrixProduct_cons {d : ℕ} (A : Square d) (w : List (Square d)) :
    matrixProduct (A :: w) = matrixProduct w * A := by
  simp [matrixProduct, List.reverse_cons, List.prod_append]

lemma matrixProduct_append {d : ℕ} (u v : List (Square d)) :
    matrixProduct (u ++ v) = matrixProduct v * matrixProduct u := by
  simp [matrixProduct, List.reverse_append, List.prod_append]

theorem matrix_product_semantics {d : ℕ} :
    matrixProduct ([] : List (Square d)) = 1 ∧
    ∀ w : List (Square d), ∀ A : Square d,
      matrixProduct (w ++ [A]) = A * matrixProduct w := by
  refine ⟨matrixProduct_nil, ?_⟩
  intro w A
  simp [matrixProduct_append]

lemma spectralNorm_nonneg {d : ℕ} (A : Square d) : 0 ≤ spectralNorm A := norm_nonneg _

lemma spectralNorm_mul_le {d : ℕ} (A B : Square d) :
    spectralNorm (A * B) ≤ spectralNorm A * spectralNorm B := by
  simpa only [spectralNorm, map_mul] using
    norm_mul_le (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A)
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) B)

lemma spectralNorm_add_le {d : ℕ} (A B : Square d) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  simpa only [spectralNorm, map_add] using
    norm_add_le (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A)
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) B)

lemma spectralNorm_one {d : ℕ} (hd : 1 ≤ d) : spectralNorm (1 : Square d) = 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  simp [spectralNorm]

lemma spectralNorm_smul {d : ℕ} (c : ℂ) (A : Square d) :
    spectralNorm (c • A) = ‖c‖ * spectralNorm A := by
  simp [spectralNorm, map_smul, norm_smul]

lemma continuous_spectralNorm {d : ℕ} : Continuous (spectralNorm (d := d)) := by
  let f : Square d →ₗ[ℂ] (EuclideanVector d →L[ℂ] EuclideanVector d) :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact f.continuous_of_finiteDimensional.norm

lemma continuous_finiteProduct {d n : ℕ} :
    Continuous (fun A : Fin n → Square d => finiteProduct A) := by
  induction n with
  | zero => simpa [finiteProduct, matrixProduct] using continuous_const
  | succ n ih =>
      have ht : Continuous (fun A : Fin (n+1) → Square d =>
          finiteProduct (fun i : Fin n => A i.succ)) :=
        ih.comp (continuous_pi fun i => continuous_apply i.succ)
      have he : (fun A : Fin (n+1) → Square d => finiteProduct A) =
          (fun A : Fin (n+1) → Square d =>
            finiteProduct (fun i : Fin n => A i.succ) * A 0) := by
        funext A
        simp [finiteProduct, List.ofFn_succ, matrixProduct_cons]
      rw [he]
      exact ht.mul (continuous_apply 0)

lemma WordIn_nil {d : ℕ} (M : Set (Square d)) : WordIn M [] := by
  simp [WordIn]

lemma WordIn_cons_iff {d : ℕ} (M : Set (Square d)) (A : Square d) (w : List (Square d)) :
    WordIn M (A :: w) ↔ A ∈ M ∧ WordIn M w := by
  simp [WordIn]

lemma WordIn_append_iff {d : ℕ} (M : Set (Square d)) (u v : List (Square d)) :
    WordIn M (u ++ v) ↔ WordIn M u ∧ WordIn M v := by
  constructor
  · intro h
    exact ⟨fun A hA => h A (List.mem_append.mpr (Or.inl hA)),
      fun A hA => h A (List.mem_append.mpr (Or.inr hA))⟩
  · rintro ⟨hu, hv⟩ A hA
    rcases List.mem_append.mp hA with hA | hA
    · exact hu A hA
    · exact hv A hA

lemma WordIn_ofFn {d n : ℕ} (M : Set (Square d)) (A : Fin n → Square d)
    (hA : ∀ i, A i ∈ M) : WordIn M (List.ofFn A) := by
  exact List.forall_mem_ofFn_iff.mpr hA

lemma word_spectralNorm_le_pow {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ A ∈ M, spectralNorm A ≤ L)
    (w : List (Square d)) (hw : WordIn M w) :
    spectralNorm (matrixProduct w) ≤ L ^ w.length := by
  induction w with
  | nil => simp [spectralNorm_one hd]
  | cons A w ih =>
      obtain ⟨hA, hw⟩ := (WordIn_cons_iff M A w).mp hw
      rw [matrixProduct_cons, List.length_cons, pow_succ]
      exact (spectralNorm_mul_le _ _).trans
        (mul_le_mul (ih hw) (hbound A hA) (spectralNorm_nonneg A) (pow_nonneg hL _))

theorem diagonal_inverse {d : ℕ} (σ : Fin d → ℝ) (hσ : ∀ i, σ i ≠ 0) :
    diagonalWeights σ * inverseDiagonalWeights σ = 1 ∧
      inverseDiagonalWeights σ * diagonalWeights σ = 1 := by
  have hz : ∀ i, (σ i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.mpr (hσ i)
  constructor <;> ext i j <;> by_cases hij : i = j <;>
    simp [diagonalWeights, inverseDiagonalWeights, Matrix.diagonal_apply,
      Matrix.one_apply, hij, hz]

#print axioms matrix_product_semantics

#print axioms diagonal_inverse

#print axioms word_spectralNorm_le_pow


end NLA.MF07
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.MF07.ProductEnvelope -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original approximate-extremal-norm argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The norm is constructed from actual words. Its finiteness, definiteness,
triangle inequality, complex homogeneity and generator inequality are proved.
The same construction will also discharge the interspersed-product estimate.
-/


set_option autoImplicit false


noncomputable section
namespace NLA.MF07

@[simp] lemma applyMatrix_one {d : ℕ} (x : EuclideanVector d) :
    applyMatrix (1 : Square d) x = x := by
  simp [applyMatrix]

lemma applyMatrix_mul {d : ℕ} (A B : Square d) (x : EuclideanVector d) :
    applyMatrix (A * B) x = applyMatrix A (applyMatrix B x) := by
  simp [applyMatrix, map_mul]

lemma applyMatrix_add {d : ℕ} (A B : Square d) (x : EuclideanVector d) :
    applyMatrix (A + B) x = applyMatrix A x + applyMatrix B x := by
  simp [applyMatrix, map_add]

lemma applyMatrix_add_vector {d : ℕ} (A : Square d) (x y : EuclideanVector d) :
    applyMatrix A (x+y) = applyMatrix A x + applyMatrix A y := by
  exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A).map_add x y

lemma applyMatrix_smul_vector {d : ℕ} (A : Square d) (c : ℂ) (x : EuclideanVector d) :
    applyMatrix A (c • x) = c • applyMatrix A x := by
  exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A).map_smul c x

lemma norm_applyMatrix_le {d : ℕ} (A : Square d) (x : EuclideanVector d) :
    ‖applyMatrix A x‖ ≤ spectralNorm A * ‖x‖ :=
  (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A).le_opNorm x

/-- All nonnegative discounted orbit values, with the empty word included. -/
def envelopeValues {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u : ℝ) (x : EuclideanVector d) : Set ℝ :=
  {r | ∃ z : List (Square d), WordIn M z ∧
    r = (u ^ z.length)⁻¹ * ‖applyMatrix (matrixProduct (z.map C)) x‖}

def productEnvelope {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u : ℝ) (x : EuclideanVector d) : ℝ := sSup (envelopeValues M C u x)

lemma envelopeValues_empty {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u : ℝ) (x : EuclideanVector d) : ‖x‖ ∈ envelopeValues M C u x := by
  refine ⟨[], WordIn_nil M, ?_⟩
  simp

lemma envelopeValues_bddAbove {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (x : EuclideanVector d) :
    ∀ r ∈ envelopeValues M C u x, r ≤ K * ‖x‖ := by
  rintro r ⟨z, hz, rfl⟩
  have hp : 0 < u ^ z.length := pow_pos hu _
  have ha := norm_applyMatrix_le (matrixProduct (z.map C)) x
  have hb := mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg x)
  have hc := mul_le_mul_of_nonneg_left (ha.trans hb) (inv_nonneg.mpr hp.le)
  calc
    (u ^ z.length)⁻¹ * ‖applyMatrix (matrixProduct (z.map C)) x‖ ≤
        (u ^ z.length)⁻¹ * (K * u ^ z.length * ‖x‖) := hc
    _ = K * ‖x‖ := by field_simp

lemma productEnvelope_bounds {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (x : EuclideanVector d) :
    ‖x‖ ≤ productEnvelope M C u x ∧ productEnvelope M C u x ≤ K * ‖x‖ := by
  have hb := envelopeValues_bddAbove M C u K hu hC x
  exact ⟨le_csSup ⟨K * ‖x‖, hb⟩ (envelopeValues_empty M C u x),
    csSup_le ⟨‖x‖, envelopeValues_empty M C u x⟩ hb⟩

lemma envelope_word_le {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (x : EuclideanVector d) (z : List (Square d)) (hz : WordIn M z) :
    (u ^ z.length)⁻¹ * ‖applyMatrix (matrixProduct (z.map C)) x‖ ≤
      productEnvelope M C u x := by
  exact le_csSup ⟨K * ‖x‖, envelopeValues_bddAbove M C u K hu hC x⟩ ⟨z, hz, rfl⟩

lemma productEnvelope_triangle {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (x y : EuclideanVector d) :
    productEnvelope M C u (x+y) ≤ productEnvelope M C u x + productEnvelope M C u y := by
  apply csSup_le ⟨‖x+y‖, envelopeValues_empty M C u (x+y)⟩
  rintro r ⟨z, hz, rfl⟩
  rw [applyMatrix_add_vector]
  calc
    (u ^ z.length)⁻¹ * ‖applyMatrix (matrixProduct (z.map C)) x +
        applyMatrix (matrixProduct (z.map C)) y‖ ≤
        (u ^ z.length)⁻¹ * (‖applyMatrix (matrixProduct (z.map C)) x‖ +
          ‖applyMatrix (matrixProduct (z.map C)) y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ productEnvelope M C u x + productEnvelope M C u y := by
      rw [mul_add]
      exact add_le_add (envelope_word_le M C u K hu hC x z hz)
        (envelope_word_le M C u K hu hC y z hz)

lemma productEnvelope_smul_le {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (c : ℂ) (x : EuclideanVector d) :
    productEnvelope M C u (c • x) ≤ ‖c‖ * productEnvelope M C u x := by
  apply csSup_le ⟨‖c • x‖, envelopeValues_empty M C u (c • x)⟩
  rintro r ⟨z, hz, rfl⟩
  rw [applyMatrix_smul_vector, norm_smul]
  calc
    (u ^ z.length)⁻¹ * (‖c‖ * ‖applyMatrix (matrixProduct (z.map C)) x‖) =
        ‖c‖ * ((u ^ z.length)⁻¹ * ‖applyMatrix (matrixProduct (z.map C)) x‖) := by ring
    _ ≤ ‖c‖ * productEnvelope M C u x :=
      mul_le_mul_of_nonneg_left (envelope_word_le M C u K hu hC x z hz) (norm_nonneg c)

lemma productEnvelope_isComplexNorm {d : ℕ} (M : Set (Square d))
    (C : Square d → Square d) (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length) :
    IsComplexNorm (productEnvelope M C u) := by
  have hb := productEnvelope_bounds M C u K hu hC
  have hnonneg : ∀ x, 0 ≤ productEnvelope M C u x := fun x => (norm_nonneg x).trans (hb x).1
  have hz : productEnvelope M C u 0 = 0 := by
    exact le_antisymm (by simpa using (hb 0).2) (hnonneg 0)
  refine ⟨hnonneg, ?_, productEnvelope_triangle M C u K hu hC, ?_⟩
  · intro x
    constructor
    · intro hx
      have hnx : ‖x‖ ≤ 0 := by simpa [hx] using (hb x).1
      exact norm_eq_zero.mp (le_antisymm hnx (norm_nonneg x))
    · rintro rfl
      exact hz
  · intro c x
    apply le_antisymm (productEnvelope_smul_le M C u K hu hC c x)
    by_cases hc : c = 0
    · simp [hc, hz]
    · have hback := productEnvelope_smul_le M C u K hu hC c⁻¹ (c • x)
      rw [inv_smul_smul₀ hc] at hback
      have hmul := mul_le_mul_of_nonneg_left hback (norm_nonneg c)
      simpa [norm_inv, mul_assoc, norm_ne_zero_iff.mpr hc] using hmul

lemma productEnvelope_generator {d : ℕ} (M : Set (Square d))
    (C : Square d → Square d) (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (A : Square d) (hA : A ∈ M) (x : EuclideanVector d) :
    productEnvelope M C u (applyMatrix (C A) x) ≤ u * productEnvelope M C u x := by
  apply csSup_le ⟨_, envelopeValues_empty M C u _⟩
  rintro r ⟨z, hz, rfl⟩
  have hword : WordIn M (A :: z) := (WordIn_cons_iff M A z).mpr ⟨hA, hz⟩
  have hw := envelope_word_le M C u K hu hC x (A :: z) hword
  have hp : u ^ z.length ≠ 0 := pow_ne_zero _ hu.ne'
  have he : (u ^ z.length)⁻¹ *
        ‖applyMatrix (matrixProduct (z.map C)) (applyMatrix (C A) x)‖ =
      u * ((u ^ (A :: z).length)⁻¹ *
        ‖applyMatrix (matrixProduct ((A :: z).map C)) x‖) := by
    simp only [List.map_cons, matrixProduct_cons, applyMatrix_mul, List.length_cons, pow_succ]
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hw hu.le

#print axioms productEnvelope_isComplexNorm

#print axioms productEnvelope_generator


end NLA.MF07
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.MF05.Definitions -/
/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance; statement draft, not a completed proof.

Original mathematical proof: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge, Theorem 2,
Proposition 5 and Corollary 7 of uniform_growth_and_holder.tex.

The actual matrix, word, norm and radius definitions and discounted word
envelope are reused unchanged from the published NLA.MF07 development.
Nothing here assumes a limit theorem, an extremal norm, or continuity of the
joint spectral radius. The independent Challenge supplies those obligations.
-/



set_option autoImplicit false

noncomputable section
namespace NLA.MF05
open NLA.MF07

/-- Matrices act on the actual complex Euclidean space. Its continuous-linear
operator metric uses precisely the spectral norm, not an entrywise matrix norm. -/
def spectralImage {d : ℕ} (M : Set (Square d)) :
    Set (EuclideanVector d →L[ℂ] EuclideanVector d) :=
  (fun A : Square d => Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A) '' M

/-- The literal infimum in the canonical spectral Hausdorff formula.
Nonempty compact families are required by all correspondence contracts. -/
def pointFamilyDistance {d : ℕ} (A : Square d) (N : Set (Square d)) : ℝ :=
  sInf ((fun B : Square d => spectralNorm (A - B)) '' N)

/-- The directed supremum in the canonical formula. -/
def directedSpectralDistance {d : ℕ} (M N : Set (Square d)) : ℝ :=
  sSup ((fun A : Square d => pointFamilyDistance A N) '' M)

/-- The original max-of-two-sup-inf formula, with the actual spectral norm. -/
def canonicalHausdorff {d : ℕ} (M N : Set (Square d)) : ℝ :=
  max (directedSpectralDistance M N) (directedSpectralDistance N M)

/-- Mathlib's Hausdorff distance of the spectral operator images. Its equality
with `canonicalHausdorff`, finiteness and nearest generators must be proved;
the library's total definition on empty/unbounded sets is never a hypothesis
substitute for nonempty compact families in the target. -/
def spectralHausdorff {d : ℕ} (M N : Set (Square d)) : ℝ :=
  Metric.hausdorffDist (spectralImage M) (spectralImage N)

/-- Scalar multiplication of every actual generator, with no radius condition. -/
def scaledFamily {d : ℕ} (c : ℝ) (M : Set (Square d)) : Set (Square d) :=
  (fun A : Square d => (c : ℂ) • A) '' M

/-- Adjoin the actual scalar identity. No radius formula is built into it. -/
def identityAdjoin {d : ℕ} (e : ℝ) (M : Set (Square d)) : Set (Square d) :=
  insert ((e : ℂ) • (1 : Square d)) M

/-- All generators lie in one spectral-norm ball; no cardinality restriction. -/
def InNormBall {d : ℕ} (M : Set (Square d)) (L : ℝ) : Prop :=
  ∀ A ∈ M, spectralNorm A ≤ L

def comparisonFactor (d : ℕ) (s : ℝ) : ℝ :=
  (d : ℝ) * s ^ (d - 1)

def comparisonRate (d : ℕ) (M : Set (Square d)) (L s : ℝ) : ℝ :=
  jointSpectralRadius M + 2 * (d : ℝ) ^ 2 * L / s

/-- The concrete supremum of discounted word actions, with the empty word
included. Its finiteness, four complex norm axioms and generator bound are
conclusions of `controlled_comparison_norm`, not assumed structure fields. -/
def comparisonNorm (d : ℕ) (M : Set (Square d)) (L s : ℝ)
    (x : EuclideanVector d) : ℝ :=
  productEnvelope M (fun A => A) (comparisonRate d M L s) x

/-- The symbolic positive d-th-root scale used when 0 < delta ≤ L. -/
def holderScale (d : ℕ) (L delta : ℝ) : ℝ :=
  Real.rpow (L / delta) (1 / (d : ℝ))

/-- The manuscript's uniform, nonoptimal constant; d=1 remains included.
The sharper scalar Lipschitz constant and exponent sharpness are not targets. -/
def holderConstant (d : ℕ) (L : ℝ) : ℝ :=
  (d : ℝ) * (2 * (d : ℝ) + 1) * Real.rpow L (1 - 1 / (d : ℝ))

/-- The sole new fixed rational numerical certificate concerns this radius. -/
def localRadius : ℝ := 1 / 2

def localNormBound {d : ℕ} (M0 : Set (Square d)) : ℝ := familyNorm M0 + 1

end NLA.MF05
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.MF05.PaperRealDefinitions -/


/- Real-matrix semantics and the entrywise complex embedding; no claims assumed. -/
set_option autoImplicit false
noncomputable section
namespace NLA.MF05.Paper

abbrev RealSquare (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev RealVector (d : ℕ) := EuclideanSpace ℝ (Fin d)

def complexify {d : ℕ} : RealSquare d →+* NLA.MF07.Square d :=
  Complex.ofRealHom.mapMatrix

def realSpectralNorm {d : ℕ} (A : RealSquare d) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜:=ℝ) A‖

def realMatrixProduct {d : ℕ} (w : List (RealSquare d)) : RealSquare d := w.reverse.prod
def realWordNorms {d : ℕ} (M : Set (RealSquare d)) (n : ℕ) : Set ℝ :=
  {r | ∃ w : List (RealSquare d), w.length = n ∧ (∀ A ∈ w, A ∈ M) ∧
    r = realSpectralNorm (realMatrixProduct w)}
def realFamilyGrowth {d : ℕ} (M : Set (RealSquare d)) (n : ℕ) := sSup (realWordNorms M n)
def realRootGrowth {d : ℕ} (M : Set (RealSquare d)) (n : ℕ) :=
  Real.rpow (realFamilyGrowth M n) (1/(n:ℝ))
def realRadius {d : ℕ} (M : Set (RealSquare d)) : ℝ :=
  sInf {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = realRootGrowth M n}

def realPointDistance {d : ℕ} (A : RealSquare d) (N : Set (RealSquare d)) : ℝ :=
  sInf ((fun B => realSpectralNorm (A-B)) '' N)
def realDirectedDistance {d : ℕ} (M N : Set (RealSquare d)) : ℝ :=
  sSup ((fun A => realPointDistance A N) '' M)
def realHausdorff {d : ℕ} (M N : Set (RealSquare d)) : ℝ :=
  max (realDirectedDistance M N) (realDirectedDistance N M)

end NLA.MF05.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.MF05.PaperGrowthDefinitions -/


/- The exact constant in main.tex, without its archive enlargement to 3. -/
set_option autoImplicit false
noncomputable section
namespace NLA.MF05.Paper

def theta (d : ℕ) : ℝ :=
  if d ≤ 1 then 1 else
    (d : ℝ) * (2 * Real.exp 1 * (d : ℝ)^2 / ((d-1 : ℕ) : ℝ))^(d-1)

end NLA.MF05.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.MF05.GrowthChallenge -/


set_option autoImplicit false
open scoped Topology Matrix.Norms.L2Operator
open NLA.MF07 Filter
noncomputable section
namespace NLA.MF05.Paper

theorem paper_real_bounded_positive_radius_growth {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (hr : 0 < realRadius M) (n : ℕ) (hn : 1 ≤ n) :
    realFamilyGrowth M n ≤ theta d * (L*(n : ℝ))^(d-1) *
      (realRadius M)^((n : ℤ)-(d : ℤ)+1) := by
  sorry

theorem paper_real_bounded_zero_radius_nilpotent {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (hr : realRadius M = 0)
    (w : List (RealSquare d)) (hw : ∀ A ∈ w, A ∈ M) (hlen : d ≤ w.length) :
    realMatrixProduct w = 0 := by
  sorry

end NLA.MF05.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: PaperChallenge -/


set_option autoImplicit false
open scoped Topology
open NLA.MF07 Filter
noncomputable section
namespace NLA.MF05.Paper

theorem paper_real_uniform_holder {d : ℕ} (hd : 1 ≤ d) (M N : Set (RealSquare d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L)
    (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (hNL : ∀ A ∈ N, realSpectralNorm A ≤ L) :
    |realRadius M - realRadius N| ≤
      (d : ℝ)*(2*(d : ℝ)+1) * Real.rpow L (1-1/(d : ℝ)) *
        Real.rpow (realHausdorff M N) (1/(d : ℝ)) := by
  sorry

end NLA.MF05.Paper
end
end
