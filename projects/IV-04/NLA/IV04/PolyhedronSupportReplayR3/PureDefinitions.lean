module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Finset.Max
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Tactic
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.DiophantineApproximation.ContinuedFractions
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

@[expose] public section

/- Actual finite real inequality systems; no vertex/certificate/runtime contracts. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

 def feasible {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i, (A *ᵥ x) i ≤ b i

 def feasibleSet {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) : Set (Fin n → ℝ) :=
  {x | feasible A b x}

 def tightRows {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x : Fin n → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => (A *ᵥ x) i = b i)

 def lineFree {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) : Prop :=
  ∀ x d : Fin n → ℝ, (∀ t : ℝ, feasible A b (x+t • d)) → d=0

end
end Reference.IV04AffinePolyhedronSteps

/- Actual affine-line exclusion in an arbitrary signed coordinate orthant. -/

set_option autoImplicit false
namespace Reference.IV04ExactOutputSupport


end Reference.IV04ExactOutputSupport

/- Reference-only arithmetic facts for exact rational endpoint recovery.
   No polyhedron, certificate, oracle correctness, or runtime contract is assumed. -/

set_option autoImplicit false
namespace Reference.IV04ExactOutputSupport


end Reference.IV04ExactOutputSupport

/- The actual minimum positive slack ratio gives a feasible step and a new tight row. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix


end
end Reference.IV04AffinePolyhedronSteps

/- Endpoint recovery includes equality at the lower bracket; literal quarter-gap midpoint bound. -/

set_option autoImplicit false
namespace Reference.IV04ExactOutputSupport


end Reference.IV04ExactOutputSupport

/- Finite actual tight-cardinality maximization; no vertex witness is supplied. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix


end
end Reference.IV04AffinePolyhedronSteps

/- Actual trivial tight kernel makes the actual feasible point an extreme point. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix


end
end Reference.IV04AffinePolyhedronSteps

/- The signed orthant is encoded as actual added matrix inequalities. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

 def withOrthant {ι : Type*} {n : ℕ} (A : Matrix ι (Fin n) ℝ)
    (s : Fin n → ℝ) : Matrix (ι ⊕ Fin n) (Fin n) ℝ
  | Sum.inl i, j => A i j
  | Sum.inr i, j => if i=j then -s i else 0

 def withOrthantBounds {ι : Type*} {n : ℕ} (b : ι → ℝ) : ι ⊕ Fin n → ℝ
  | Sum.inl i => b i
  | Sum.inr _ => 0

 def signedFeasibleSet {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (s : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | feasible A b x ∧ ∀ j, 0 ≤ s j*x j}

end
end Reference.IV04AffinePolyhedronSteps

/- Actual linear objectives and bounded recession directions; original constraints only. -/

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps


end
end Reference.IV04OriginalObjectiveAttainment

/- Genuine rational recovery from the actual full tight system, via its actual Gram matrix. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

 def realMatrix {ι κ : Type*} (A : Matrix ι κ ℚ) : Matrix ι κ ℝ :=
  A.map (Rat.castHom ℝ)

 def realVector {ι : Type*} (b : ι → ℚ) : ι → ℝ := fun i => b i

 def activeMatrix {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (x : Fin n → ℝ) : Matrix ι (Fin n) ℚ := by
  classical
  exact fun i j => if i ∈ tightRows (realMatrix A) (realVector b) x then A i j else 0

 def activeBounds {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (x : Fin n → ℝ) : ι → ℚ := by
  classical
  exact fun i => if i ∈ tightRows (realMatrix A) (realVector b) x then b i else 0

 def cramerCandidate {n : ℕ} (G : Matrix (Fin n) (Fin n) ℚ) (c : Fin n → ℚ) :
    Fin n → ℚ := fun j => G.cramer c j/G.det

end
end Reference.IV04AffinePolyhedronSteps

/- An original extreme point dominates any feasible point for an actually bounded linear objective. -/

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps


end
end Reference.IV04OriginalObjectiveAttainment

/- Honest determinant bounds for an integer Gram system and its Cramer numerators. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

def gramCertificateBound (m n H : ℕ) : ℕ := n.factorial*(m*H^2)^n

end
end Reference.IV04AffinePolyhedronSteps

/- Rational extreme points of the original signed-orthant inequalities. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

def rationalWithOrthant {ι : Type*} {n : ℕ} (A : Matrix ι (Fin n) ℚ)
    (s : Fin n → ℚ) : Matrix (ι ⊕ Fin n) (Fin n) ℚ
  | Sum.inl i, j => A i j
  | Sum.inr i, j => if i=j then -s i else 0

def rationalWithOrthantBounds {ι : Type*} {n : ℕ} (b : ι → ℚ) : ι ⊕ Fin n → ℚ
  | Sum.inl i => b i
  | Sum.inr _ => 0

end
end Reference.IV04AffinePolyhedronSteps

/- Finite actual original-row Gram candidates; no threshold facet is added. -/

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps

def maskedMatrix {ι : Type*} [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (I : Finset ι) : Matrix ι (Fin n) ℚ :=
  fun i j => if i ∈ I then A i j else 0
def maskedBounds {ι : Type*} [DecidableEq ι] (b : ι → ℚ) (I : Finset ι) : ι → ℚ :=
  fun i => if i ∈ I then b i else 0
def originalMaskCandidate {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) (I : Finset ι) : Fin n → ℚ :=
  cramerCandidate ((maskedMatrix A I)ᵀ*maskedMatrix A I)
    ((maskedMatrix A I)ᵀ *ᵥ maskedBounds b I)
def feasibleCandidateMasks {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b : ι → ℚ) : Finset (Finset ι) := by
  classical
  exact Finset.univ.filter (fun I => feasible (realMatrix A) (realVector b)
    (realVector (originalMaskCandidate A b I)))

end
end Reference.IV04OriginalObjectiveAttainment

/- An explicit polynomial exponent for the honest Gram determinant bound. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps


end Reference.IV04AffinePolyhedronSteps

/- Actual integer Gram/Cramer certificates of a real solution of a full-column-rank system. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

def integerRealMatrix {ι κ : Type*} (M : Matrix ι κ ℤ) : Matrix ι κ ℝ :=
  M.map (Int.castRingHom ℝ)
def integerRealVector {ι : Type*} (b : ι → ℤ) : ι → ℝ := fun i => b i

end
end Reference.IV04AffinePolyhedronSteps

/- Bounded actual objectives attain a rational original extreme point, using finite original-row candidates. -/

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps


end
end Reference.IV04OriginalObjectiveAttainment

/- Bounded integer numerator/common-denominator certificates from original pointed inequalities. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix


end
end Reference.IV04AffinePolyhedronSteps

/- The honest original-row bound applies to every actual trivial-tight-kernel point. -/

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps


end
end Reference.IV04OriginalObjectiveAttainment

/- Bound for an actual extreme point of original integer signed-orthant inequalities. -/

set_option autoImplicit false
namespace Reference.IV04AffinePolyhedronSteps
noncomputable section
open scoped Matrix

def integerWithOrthant {ι : Type*} {n : ℕ} (A : Matrix ι (Fin n) ℤ)
    (s : Fin n → ℤ) : Matrix (ι ⊕ Fin n) (Fin n) ℤ
  | Sum.inl i,j => A i j
  | Sum.inr i,j => if i=j then -s i else 0
def integerWithOrthantBounds {ι : Type*} {n : ℕ} (b : ι → ℤ) : ι ⊕ Fin n → ℤ
  | Sum.inl i => b i
  | Sum.inr _ => 0

end
end Reference.IV04AffinePolyhedronSteps

/- Actual reduced denominator bounds from an actual integer fraction. -/

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment


end Reference.IV04OriginalObjectiveAttainment

/- Original integer polyhedra attain bounded objectives at rational vertices with reduced size bounds. -/

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps

def integerRationalMatrix {ι κ : Type*} (A : Matrix ι κ ℤ) : Matrix ι κ ℚ :=
  A.map (Int.castRingHom ℚ)
def integerRationalVector {ι : Type*} (b : ι → ℤ) : ι → ℚ := fun i => b i

end
end Reference.IV04OriginalObjectiveAttainment
