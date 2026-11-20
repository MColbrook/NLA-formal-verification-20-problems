module

public import Mathlib

@[expose] public section

/-!
Standalone statement surface for PF-02.
Definitions and selected theorem types are retained from the original sources.
Historical notices below are preserved; current review status is in the audit records.
-/


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.PaperSymmetricDefinitions -/





set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.PF02.Paper

abbrev SymIndex (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Upper-triangular coordinates, with the lower triangle filled symmetrically. -/
def symmetricMatrix (v : SymIndex n → R) : Matrix (Fin n) (Fin n) R := fun i j =>
  if h : i ≤ j then v ⟨(i,j), h⟩ else v ⟨(j,i), le_of_not_ge h⟩

def symmetricCoordinates (X : Matrix (Fin n) (Fin n) R) : SymIndex n → R :=
  fun p => X p.val.1 p.val.2

/-- The full space of symmetric matrices, including all singular matrices. -/
def symmetricSpace (n : ℕ) (R : Type*) [CommRing R] :
    Submodule R (Matrix (Fin n) (Fin n) R) where
  carrier := {X | X.transpose = X}
  zero_mem' := by simp
  add_mem' := by intro X Y hX hY; simp_all
  smul_mem' := by intro c X hX; simp_all

/-- The actual congruence map on the entire symmetric-matrix space. -/
def symmetricCongruence (S : Matrix (Fin n) (Fin n) R) :
    symmetricSpace n R →ₗ[R] symmetricSpace n R where
  toFun X := ⟨S.transpose * X.val * S, by
    have hx : X.val.transpose = X.val := X.property
    change (S.transpose * X.val * S).transpose = S.transpose * X.val * S
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hx, Matrix.mul_assoc]⟩
  map_add' X Y := by ext i j; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by ext i j; simp

end NLA.PF02.Paper
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.PositiveBasis.Definitions -/



set_option autoImplicit false
noncomputable section
namespace Reference.PF02PositiveBasis
open Matrix NLA.PF02.Paper
open scoped BigOperators MatrixOrder

def weight {n : ℕ} (p : SymIndex n) : ℝ := if p.val.1 = p.val.2 then 2 else 1

def positiveMatrix {n : ℕ} (p : SymIndex n) : Matrix (Fin n) (Fin n) ℝ :=
  (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) + weight p • symmetricMatrix (Pi.single p 1)

def traceGram {ι : Type*} [Fintype ι] {n : ℕ}
    (F : ι → Matrix (Fin n) (Fin n) ℝ) : Matrix ι ι ℝ :=
  fun p q => trace (F p * F q)

def positiveGram (n : ℕ) : Matrix (SymIndex n) (SymIndex n) ℝ :=
  fun p q => trace (positiveMatrix p * positiveMatrix q)

def positiveMatrixInt {n : ℕ} (p : SymIndex n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => 2 * (if i = j then 1 else 0) +
    (if p.val.1 = p.val.2 then 2 else 1) * symmetricMatrix (Pi.single p 1) i j

def positiveGramInt (n : ℕ) : Matrix (SymIndex n) (SymIndex n) ℤ :=
  fun p q => trace (positiveMatrixInt p * positiveMatrixInt q)

end Reference.PF02PositiveBasis
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.BlockConstruction.Definitions -/



set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockConstruction
open Matrix NLA.PF02.Paper Reference.PF02PositiveBasis
open scoped BigOperators MatrixOrder

abbrev Axis (r : ℕ) := Fin 3 ⊕ Fin r
abbrev BlockIndex (r : ℕ) := SymIndex 3 ⊕ (SymIndex r ⊕ (Fin 3 × Fin r))

def leadingEmbed {r : ℕ} (H : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Axis r) (Axis r) ℝ :=
  Matrix.fromBlocks H 0 0 0

def trailingEmbed {r : ℕ} (H : Matrix (Fin r) (Fin r) ℝ) : Matrix (Axis r) (Axis r) ℝ :=
  Matrix.fromBlocks 0 0 0 H

def offDiagonalPositive {α : Type*} [DecidableEq α] (i j : α) : Matrix α α ℝ :=
  fun a b => 2 * (if a = b then 1 else 0) + (if a = i ∧ b = j then 1 else 0) +
    (if a = j ∧ b = i then 1 else 0)

def blockFactor (r : ℕ) : BlockIndex r → Matrix (Axis r) (Axis r) ℝ
  | Sum.inl p => leadingEmbed (positiveMatrix p)
  | Sum.inr (Sum.inl p) => trailingEmbed (positiveMatrix p)
  | Sum.inr (Sum.inr ij) => offDiagonalPositive (Sum.inl ij.1) (Sum.inr ij.2)

def blockGram (r : ℕ) : Matrix (BlockIndex r) (BlockIndex r) ℝ :=
  fun p q => trace (blockFactor r p * blockFactor r q)

def finiteBlockFactor (r : ℕ) (p : BlockIndex r) : Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  (blockFactor r p).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def finiteBlockGram (r : ℕ) : Matrix (BlockIndex r) (BlockIndex r) ℝ :=
  traceGram (finiteBlockFactor r)

def blockFactorInt (r : ℕ) : BlockIndex r → Matrix (Axis r) (Axis r) ℤ
  | Sum.inl p => Matrix.fromBlocks (positiveMatrixInt p) 0 0 0
  | Sum.inr (Sum.inl p) => Matrix.fromBlocks 0 0 0 (positiveMatrixInt p)
  | Sum.inr (Sum.inr ij) => fun a b => 2 * (if a = b then 1 else 0) +
      (if a = Sum.inl ij.1 ∧ b = Sum.inr ij.2 then 1 else 0) +
      (if a = Sum.inr ij.2 ∧ b = Sum.inl ij.1 then 1 else 0)

def finiteBlockFactorInt (r : ℕ) (p : BlockIndex r) : Matrix (Fin (3+r)) (Fin (3+r)) ℤ :=
  (blockFactorInt r p).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def finiteBlockGramInt (r : ℕ) : Matrix (BlockIndex r) (BlockIndex r) ℤ :=
  fun p q => trace (finiteBlockFactorInt r p * finiteBlockFactorInt r q)

end Reference.PF02BlockConstruction
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.Definitions -/
/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
-/









noncomputable section
open Matrix
namespace NLA.PF02

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ
abbrev FactorTuple (p q k : ℕ) := (Fin p → Mat k k) × (Fin q → Mat k k)

/-- Every row and column factor is genuinely real positive semidefinite. -/
def IsFactorization {p q k : ℕ} (M : Mat p q) (F : FactorTuple p q k) : Prop :=
  (∀ i, (F.1 i).PosSemidef) ∧ (∀ j, (F.2 j).PosSemidef) ∧
    ∀ i j, Matrix.trace (F.1 i * F.2 j) = M i j

/-- The full factorization space with its inherited finite-dimensional Euclidean topology. -/
abbrev Factorization {p q : ℕ} (M : Mat p q) (k : ℕ) :=
  {F : FactorTuple p q k // IsFactorization M F}

/-- The actual minimum among all positive integer factor sizes, including attainment. -/
def IsPSDRank {p q : ℕ} (M : Mat p q) (k : ℕ) : Prop :=
  IsLeast {ℓ : ℕ | 1 ≤ ℓ ∧ Nonempty (Factorization M ℓ)} k

/-- A single genuine invertible change of basis, on all row and column factors. -/
def Congruent {p q k : ℕ} {M : Mat p q} (F G : Factorization M k) : Prop :=
  ∃ S : (Mat k k)ˣ,
    (∀ i, G.val.1 i = (↑S : Mat k k).transpose * F.val.1 i * ↑S) ∧
    (∀ j, G.val.2 j = (↑(S⁻¹) : Mat k k) * F.val.2 j * (↑(S⁻¹) : Mat k k).transpose)

/-- Quotient topology on actual congruence orbits; the public orbit theorem checks exact equality. -/
abbrev OrbitSpace {p q : ℕ} (M : Mat p q) (k : ℕ) :=
  Quot (@Congruent p q k M)

def AllMinimalOrbitsConnected : Prop :=
  ∀ (k p q : ℕ), 3 ≤ k → 1 ≤ p → 1 ≤ q → ∀ M : Mat p q,
    (∀ i j, 0 ≤ M i j) → M.rank = k * (k + 1) / 2 → IsPSDRank M k →
    IsConnected (Set.univ : Set (OrbitSpace M k))

/-- Fixed diagonal/off-diagonal coordinates on all real three-by-three matrices. -/
def coord (X : Mat 3 3) : Fin 6 → ℝ :=
  ![X 0 0, X 1 1, X 2 2, X 0 1, X 0 2, X 1 2]

def rowCoordinates (A : Fin 6 → Mat 3 3) : Mat 6 6 := fun i => coord (A i)

def orientationDet {M : Mat 6 6} (F : Factorization M 3) : ℝ :=
  (rowCoordinates F.val.1).det

def witnessM : Mat 6 6 := !![
  24,20,20,16,16,16;
  20,24,20,16,16,16;
  20,20,24,16,16,16;
  16,16,16,14,12,12;
  16,16,16,12,14,12;
  16,16,16,12,12,14]

/-- The sign parameter is used only at +1 and −1 in the two explicit tuples. -/
def witnessFactors (s : ℝ) : Fin 6 → Mat 3 3 := ![
  !![4,0,0; 0,2,0; 0,0,2],
  !![2,0,0; 0,4,0; 0,0,2],
  !![2,0,0; 0,2,0; 0,0,4],
  !![2,s,0; s,2,0; 0,0,2],
  !![2,0,1; 0,2,0; 1,0,2],
  !![2,0,0; 0,2,1; 0,1,2]]

def witnessTuple (s : ℝ) : FactorTuple 6 6 3 := (witnessFactors s, witnessFactors s)

end NLA.PF02
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.BlockConstruction.EnumeratedDefinitions -/


set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockConstruction
open Matrix

def enumeratedIntegerGram (r : ℕ) :
    Matrix (Fin (Fintype.card (BlockIndex r))) (Fin (Fintype.card (BlockIndex r))) ℤ :=
  (finiteBlockGramInt r).reindex (Fintype.equivFin (BlockIndex r)) (Fintype.equivFin (BlockIndex r))

def enumeratedRealGram (r : ℕ) :
    Matrix (Fin (Fintype.card (BlockIndex r))) (Fin (Fintype.card (BlockIndex r))) ℝ :=
  (enumeratedIntegerGram r).map (Int.castRingHom ℝ)

def enumeratedFactor (r : ℕ) (i : Fin (Fintype.card (BlockIndex r))) :
    Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  finiteBlockFactor r ((Fintype.equivFin (BlockIndex r)).symm i)

end Reference.PF02BlockConstruction
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.SupportBridge.Definitions -/
/- Actual finite real PSD support definitions. Separate reference extension. -/




set_option autoImplicit false
noncomputable section
namespace Reference.PF02Support
open Matrix
open scoped BigOperators MatrixOrder

abbrev Mat (n : Type*) := Matrix n n ℝ
abbrev Vector (n : Type*) := EuclideanSpace ℝ n

def lin {n : Type*} [Fintype n] [DecidableEq n] (A : Mat n) :
    Vector n →ₗ[ℝ] Vector n := Matrix.toEuclideanLin A

def kernel {n : Type*} [Fintype n] [DecidableEq n] (A : Mat n) :
    Submodule ℝ (Vector n) := LinearMap.ker (lin A)

def image {n : Type*} [Fintype n] [DecidableEq n] (A : Mat n) :
    Submodule ℝ (Vector n) := LinearMap.range (lin A)

def SupportedOn {n : Type*} [Fintype n] [DecidableEq n]
    (A : Mat n) (U : Submodule ℝ (Vector n)) : Prop := image A ≤ U

end Reference.PF02Support
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.GlobalOrientation.Definitions -/


set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper
open scoped BigOperators

def coordinateRows {n : ℕ} (C : SymIndex n → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (SymIndex n) (SymIndex n) ℝ := fun p q => C p q.1.1 q.1.2

def orientationPolynomial {k : ℕ} (A : SymIndex 3 → Matrix (Fin k) (Fin k) ℝ) : ℝ :=
  ∑ e : Fin 3 → Fin k, (coordinateRows (fun p => (A p).submatrix e e)).det

def frameWeight {k : ℕ} (T : Matrix (Fin k) (Fin 3) ℝ) : ℝ :=
  ∑ e : Fin 3 → Fin k, (T.submatrix e id).det ^ 4

def reflectionMask {α : Type*} [DecidableEq α] (i j a b : α) : ℝ :=
  if (a = i ∧ b = j) ∨ (a = j ∧ b = i) then -1 else 1

def entryReflection {α : Type*} [DecidableEq α] (i j : α) (A : Matrix α α ℝ) :
    Matrix α α ℝ := fun a b => reflectionMask i j a b * A a b

end Reference.PF02GlobalOrientation
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.BlockSupportRecovery.Definitions -/


set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockSupportRecovery
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction
open scoped BigOperators

def blockRows {r : ℕ} (A : Fin (Fintype.card (BlockIndex r)) →
    Matrix (Fin (3+r)) (Fin (3+r)) ℝ) (p : BlockIndex r) : Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  A (Fintype.equivFin (BlockIndex r) p)

def trailingSum {r : ℕ} (B : Fin (Fintype.card (BlockIndex r)) →
    Matrix (Fin (3+r)) (Fin (3+r)) ℝ) : Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  ∑ p : SymIndex r, blockRows B (Sum.inr (Sum.inl p))

end Reference.PF02BlockSupportRecovery
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.GlobalOrientation.ActualDefinitions -/


set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction Reference.PF02BlockSupportRecovery

def leadingRows {r : ℕ} (A : Fin (Fintype.card (BlockIndex r)) → Matrix (Fin (3+r)) (Fin (3+r)) ℝ) :
    SymIndex 3 → Matrix (Fin (3+r)) (Fin (3+r)) ℝ := fun p => blockRows A (Sum.inl p)

end Reference.PF02GlobalOrientation
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.GlobalOrientation.WitnessDefinitions -/


set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction Reference.PF02PositiveBasis

def reflectedPair : SymIndex 3 := ⟨(0,1), by decide⟩

def reflectionDiagonal : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

def reflectedPositive (p : SymIndex 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  if p = reflectedPair then reflectionDiagonal.transpose * positiveMatrix p * reflectionDiagonal
  else positiveMatrix p

def reflectedBlockFactor (r : ℕ) : BlockIndex r → Matrix (Axis r) (Axis r) ℝ
  | Sum.inl p => leadingEmbed (reflectedPositive p)
  | Sum.inr p => blockFactor r (Sum.inr p)

def finiteReflectedBlockFactor (r : ℕ) (p : BlockIndex r) : Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  (reflectedBlockFactor r p).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def enumeratedReflectedFactor (r : ℕ) (i : Fin (Fintype.card (BlockIndex r))) :
    Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  finiteReflectedBlockFactor r ((Fintype.equivFin (BlockIndex r)).symm i)

def canonicalLeadingFrame (r : ℕ) : Matrix (Fin (3+r)) (Fin 3) ℝ :=
  (Matrix.fromRows (1 : Matrix (Fin 3) (Fin 3) ℝ) (0 : Matrix (Fin r) (Fin 3) ℝ)).submatrix
    finSumFinEquiv.symm id

end Reference.PF02GlobalOrientation
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.GlobalOrientation.SignDefinitions -/

set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Reference.PF02BlockConstruction

def fiberSign {r : ℕ} (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r)) : Bool :=
  decide (0 < orientationPolynomial (leadingRows F.val.1))

end Reference.PF02GlobalOrientation
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.Normalization.Definitions -/

set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Reference.PF02Support
open scoped BigOperators MatrixOrder

def rowSum {p k : ℕ} (A : Fin p → Mat (Fin k)) : Mat (Fin k) := ∑ i, A i

def rootSum {p k : ℕ} (A : Fin p → Mat (Fin k)) : Mat (Fin k) := CFC.sqrt (rowSum A)

def normalizedRow {p k : ℕ} (A : Fin p → Mat (Fin k)) (i : Fin p) : Mat (Fin k) :=
  (rootSum A)⁻¹ * A i * (rootSum A)⁻¹

def normalizedColumn {p q k : ℕ} (A : Fin p → Mat (Fin k))
    (B : Fin q → Mat (Fin k)) (j : Fin q) : Mat (Fin k) :=
  rootSum A * B j * rootSum A
end Reference.PF02Normalization
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.Normalization.CompactDefinitions -/

set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Reference.PF02Support
open scoped BigOperators MatrixOrder
abbrev FactorPair (p q k : ℕ) := (Fin p → Mat (Fin k)) × (Fin q → Mat (Fin k))
def normalizedFactorSet {p q k : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : Set (FactorPair p q k) :=
  {F | (∀ i, (F.1 i).PosSemidef) ∧ (∀ j, (F.2 j).PosSemidef) ∧
    rowSum F.1 = 1 ∧ ∀ i j, Matrix.trace (F.1 i * F.2 j) = M i j}
end Reference.PF02Normalization
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.JointCompactness.Definitions -/

set_option autoImplicit false
noncomputable section
namespace Reference.PF02JointCompactness
open Matrix Reference.PF02Support Reference.PF02Normalization
open scoped BigOperators MatrixOrder

def normalizedConstraintSet {p q k : ℕ} :
    Set (Matrix (Fin p) (Fin q) ℝ × FactorPair p q k) :=
  {Z | Z.2 ∈ normalizedFactorSet Z.1}

def jointNormalizedFactorSet {p q k : ℕ} (M : ℝ → Matrix (Fin p) (Fin q) ℝ)
    (a b : ℝ) : Set (ℝ × FactorPair p q k) :=
  {Z | Z.1 ∈ Set.Icc a b ∧ Z.2 ∈ normalizedFactorSet (M Z.1)}

def perturbedGram {p k : ℕ} (F : Fin p → Mat (Fin k)) (η : ℝ) : Mat (Fin p) :=
  fun i j => Matrix.trace ((F i + η • (1 : Mat (Fin k))) *
    (F j + η • (1 : Mat (Fin k))))
end Reference.PF02JointCompactness
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.UniformPositiveOrientation.Definitions -/


set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization

def orthogonalSet (k : ℕ) : Set (Matrix (Fin k) (Fin k) ℝ) := {O | O * O.transpose = 1}

def perturbedBlockGram (r : ℕ) (η : ℝ) :
    Matrix (Fin (Fintype.card (BlockIndex r))) (Fin (Fintype.card (BlockIndex r))) ℝ :=
  Reference.PF02JointCompactness.perturbedGram (enumeratedFactor r) η

def normalizedOrientationProduct {r : ℕ}
    (F : FactorPair (Fintype.card (BlockIndex r)) (Fintype.card (BlockIndex r)) (3+r))
    (O : Matrix (Fin (3+r)) (Fin (3+r)) ℝ) : ℝ :=
  orientationPolynomial (leadingRows F.1) *
    orientationPolynomial (fun p => O.transpose * leadingRows F.1 p * O)

end Reference.PF02UniformPositiveOrientation
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.UniformPositiveOrientation.CovarianceDefinitions -/

set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02Normalization Reference.PF02Support

def normalizingCongruence {p k : ℕ} (A C : Fin p → Mat (Fin k)) (S : Mat (Fin k)) : Mat (Fin k) :=
  rootSum A * S * (rootSum C)⁻¹

end Reference.PF02UniformPositiveOrientation
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.UniformPositiveOrientation.PerturbationDefinitions -/

set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization

def shiftedFactors {p k : ℕ} (A : Fin p → Matrix (Fin k) (Fin k) ℝ) (η : ℝ)
    (i : Fin p) : Matrix (Fin k) (Fin k) ℝ := A i + η • 1

def normalizedFiberSign {r : ℕ} {η : ℝ}
    (F : NLA.PF02.Factorization (perturbedBlockGram r η) (3+r)) : Bool :=
  decide (0 < orientationPolynomial (leadingRows (r := r) (normalizedRow F.val.1)))

end Reference.PF02UniformPositiveOrientation
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.UniformPositiveOrientation.WitnessDefinitions -/


set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization

def normalizedWitnessProduct (r : ℕ) (η : ℝ) : ℝ :=
  orientationPolynomial (leadingRows (r := r) (normalizedRow (shiftedFactors (enumeratedFactor r) η))) *
  orientationPolynomial (leadingRows (r := r) (normalizedRow (shiftedFactors (enumeratedReflectedFactor r) η)))
end Reference.PF02UniformPositiveOrientation
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.UniformPositiveOrientation.RationalDefinitions -/

set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02BlockConstruction

def enumeratedIntegerFactor (r : ℕ) (i : Fin (Fintype.card (BlockIndex r))) :
    Matrix (Fin (3+r)) (Fin (3+r)) ℤ :=
  finiteBlockFactorInt r ((Fintype.equivFin (BlockIndex r)).symm i)

def rationalPerturbedGram (r : ℕ) (q : ℚ) :
    Matrix (Fin (Fintype.card (BlockIndex r))) (Fin (Fintype.card (BlockIndex r))) ℚ :=
  fun i j => (enumeratedIntegerGram r i j : ℚ) +
    q * ((enumeratedIntegerFactor r i).trace : ℚ) +
    q * ((enumeratedIntegerFactor r j).trace : ℚ) + q^2 * (3+r)
end Reference.PF02UniformPositiveOrientation
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.UniformPositiveOrientation.RegularDefinitions -/

set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02Normalization Reference.PF02BlockConstruction

def regularParameter (r : ℕ) (η : ℝ) : Prop :=
  (perturbedBlockGram r η).rank = (3+r)*(3+r+1)/2 ∧
  ∀ F : FactorPair (Fintype.card (BlockIndex r)) (Fintype.card (BlockIndex r)) (3+r),
    F ∈ normalizedFactorSet (k := 3+r) (perturbedBlockGram r η) →
    ∀ O : Matrix (Fin (3+r)) (Fin (3+r)) ℝ, O ∈ orthogonalSet (3+r) →
      0 < normalizedOrientationProduct (r := r) F O
end Reference.PF02UniformPositiveOrientation
end
end


section -- Isolate source-module options, opened names, and local attributes.
/- Original module: NLA.PF02.PaperAllSizePSDChallenge -/


set_option autoImplicit false
namespace Reference.PF02UniformPositiveOrientation
open Matrix
theorem paper_all_size_disconnected_witness {k : ℕ} (hk : 3 ≤ k) :
  (∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℤ),
      N = k*(k+1)/2 ∧ (∀ i j, 0 ≤ M i j) ∧
      (M.map (Int.castRingHom ℝ)).rank = N ∧ NLA.PF02.IsPSDRank (M.map (Int.castRingHom ℝ)) k ∧
      ¬ IsConnected (Set.univ : Set (NLA.PF02.OrbitSpace (M.map (Int.castRingHom ℝ)) k))) ∧
  (∃ (N : ℕ) (M : Matrix (Fin N) (Fin N) ℚ), N = k*(k+1)/2 ∧
      (∀ i j, 0 < M i j) ∧ (M.map (Rat.castHom ℝ)).rank = N ∧
      NLA.PF02.IsPSDRank (M.map (Rat.castHom ℝ)) k ∧
      ¬ IsConnected (Set.univ : Set (NLA.PF02.OrbitSpace (M.map (Rat.castHom ℝ)) k))) := by
  sorry
end Reference.PF02UniformPositiveOrientation
end
