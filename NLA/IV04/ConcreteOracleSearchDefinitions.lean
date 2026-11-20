module

/- Pure shared semantic bodies: no desired recovery or certificate proof imports. -/
public import NLA.IV04.InequalityFeasibilityDefinitions
public import NLA.IV04.AffinePolyhedronSteps.Definitions
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace Reference.IV04ConcreteOracleSearch
open Complexity IV04.Paper.Computational
open scoped Matrix
def polynomialInequalitySystemVerifier (input : List Bool) : List Bool :=
  IV04.Paper.InequalityVerifier.polynomialInequalitySystemVerifier input
def inequalityIntegerWord (z : ℤ) : List Bool :=
  IV04.Paper.InequalityVerifier.inequalityIntegerWord z
def integerVectorList {n : ℕ} (p : Fin n → ℤ) : List ℤ := List.ofFn p
def inequalityIntegerCertificateCode (numerators : List ℤ) (denominator : ℕ) : List Bool :=
  pair (payloadListCode (numerators.map inequalityIntegerWord)) denominator.bits
def integerMatrixRowCode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (i : Fin m) : List Bool :=
  pair (payloadListCode ((List.ofFn (A i)).map inequalityIntegerWord)) (inequalityIntegerWord (b i))
def integerMatrixInstanceCode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) : List Bool := payloadListCode (List.ofFn (integerMatrixRowCode A b))
def inequalityInstanceLengthPolynomial (N : ℕ) : ℕ := (4*N+1)*(5*N*N+3)
def integerRealMatrix {ι κ : Type*} (M : Matrix ι κ ℤ) : Matrix ι κ ℝ := fun i j => M i j
def integerRealVector {ι : Type*} (b : ι → ℤ) : ι → ℝ := fun i => b i
def realMatrix {ι κ : Type*} (M : Matrix ι κ ℚ) : Matrix ι κ ℝ := fun i j => M i j
def realVector {ι : Type*} (b : ι → ℚ) : ι → ℝ := fun i => b i
def sharpCertificateBound (n H : ℕ) : ℕ := n.factorial*H^n
def cappedPrefixFeasibilityLanguage : Language :=
  IV04.Paper.InequalityFeasibility.cappedPrefixFeasibilityLanguage
def acceptedCertificate (instanceCode certificate : List Bool) : Prop :=
  polynomialInequalitySystemVerifier (pair instanceCode certificate)=[true]

instance (instanceCode certificate : List Bool) : Decidable (acceptedCertificate instanceCode certificate) :=
  inferInstanceAs (Decidable (polynomialInequalitySystemVerifier (pair instanceCode certificate)=[true]))

structure PrefixQuery where
  instanceCode : List Bool
  bound : ℕ
  stem : List Bool

def prefixMembership (q : PrefixQuery) : Prop :=
  ∃ tail : List Bool, (q.stem++tail).length≤q.bound ∧
    acceptedCertificate q.instanceCode (q.stem++tail)

inductive QueryProgram (α : Type) where
  | done : α → QueryProgram α
  | ask : PrefixQuery → (Bool → QueryProgram α) → QueryProgram α

noncomputable def execute {α : Type} : QueryProgram α → α
  | .done a => a
  | .ask q next => execute (next (by classical exact decide (prefixMembership q)))

def queriesAtMost {α : Type} : ℕ → QueryProgram α → Prop
  | _, .done _ => True
  | 0, .ask _ _ => False
  | k+1, .ask _ next => ∀ answer, queriesAtMost k (next answer)

def selfReduce (instanceCode : List Bool) (bound : ℕ) :
    ℕ → List Bool → QueryProgram (Option (List Bool))
  | 0,stem => .done (if acceptedCertificate instanceCode stem then some stem else none)
  | fuel+1,stem =>
    if acceptedCertificate instanceCode stem then .done (some stem)
    else .ask ⟨instanceCode,bound,stem++[false]⟩ (fun answer =>
      selfReduce instanceCode bound fuel (stem++[!answer]))

def thresholdMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (j : Fin n) (r : ℚ) : Matrix (Fin (m+1)) (Fin n) ℤ :=
  fun i k => Fin.cases (if k=j then -(r.den : ℤ) else 0) (fun i => A i k) i

def thresholdBounds {m : ℕ} (b : Fin m → ℤ) (r : ℚ) : Fin (m+1) → ℤ :=
  Fin.cases (-r.num) b

def thresholdQuery {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (j : Fin n) (r : ℚ) : PrefixQuery :=
  let instanceCode := integerMatrixInstanceCode (thresholdMatrix A j r) (thresholdBounds b r)
  ⟨instanceCode,inequalityInstanceLengthPolynomial instanceCode.length,[]⟩

def binarySearch {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (j : Fin n) : ℕ → ℚ → ℚ → QueryProgram (ℚ × ℚ)
  | 0,lower,upper => .done (lower,upper)
  | fuel+1,lower,upper =>
    let midpoint := (lower+upper)/2
    .ask (thresholdQuery A b j midpoint) (fun answer =>
      if answer then binarySearch A b j fuel midpoint upper
      else binarySearch A b j fuel lower midpoint)

def payloadNth : ℕ → List Bool → List Bool
  | 0,code => pairFst code
  | k+1,code => payloadNth k (pairSnd code)

def certificateCoordinate (j : ℕ) (certificate : List Bool) : ℚ :=
  (signedWordValue (payloadNth j (pairFst certificate)) : ℚ)/
    (wordValue (pairSnd certificate) : ℚ)

def certificatePoint (n : ℕ) (certificate : List Bool) : Fin n → ℚ :=
  fun j => certificateCoordinate j.val certificate

def cappedThresholdQuery {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (j : Fin n) (r : ℚ) (bound : ℕ) : PrefixQuery :=
  ⟨integerMatrixInstanceCode (thresholdMatrix A j r) (thresholdBounds b r),bound,[]⟩

def cappedBinarySearch {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (j : Fin n) (bound : ℕ) : ℕ → ℚ → ℚ → QueryProgram (ℚ × ℚ)
  | 0,lower,upper => .done (lower,upper)
  | fuel+1,lower,upper =>
    let midpoint := (lower+upper)/2
    .ask (cappedThresholdQuery A b j midpoint bound) (fun answer =>
      if answer then cappedBinarySearch A b j bound fuel midpoint upper
      else cappedBinarySearch A b j bound fuel lower midpoint)

def bindProgram {α β : Type} : QueryProgram α → (α → QueryProgram β) → QueryProgram β
  | .done a,f => f a
  | .ask q next,f => .ask q (fun answer => bindProgram (next answer) f)

noncomputable def executeCounting {α : Type} : QueryProgram α → α × ℕ
  | .done a => (a,0)
  | .ask q next =>
    let result := executeCounting (next (by classical exact decide (prefixMembership q)))
    (result.1,result.2+1)

def coordinateRecovery {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (j : Fin n) (bound fuel : ℕ) (lower upper : ℚ) : QueryProgram (Option ℚ) :=
  bindProgram (cappedBinarySearch A b j bound fuel lower upper) (fun bracket =>
    let instanceCode := integerMatrixInstanceCode (thresholdMatrix A j bracket.1) (thresholdBounds b bracket.1)
    bindProgram (selfReduce instanceCode bound bound []) (fun result =>
      .done (result.map (certificateCoordinate j.val))))

def encodedQuery (q : PrefixQuery) : List Bool :=
  pair q.instanceCode (pair (List.replicate q.bound true) q.stem)

def boundedCoordinateRecovery {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (j : Fin n) (bound : ℕ) : QueryProgram (Option ℚ) :=
  coordinateRecovery A b j bound (3*bound+2) (-((2 : ℚ)^bound)) ((2 : ℚ)^bound)

def queryCapsValid {α : Type} : QueryProgram α → Prop
  | .done _ => True
  | .ask q next => q.bound≤ inequalityInstanceLengthPolynomial q.instanceCode.length ∧
    ∀ answer, queryCapsValid (next answer)

noncomputable def executeActualNP {α : Type} : QueryProgram α → α × ℕ
  | .done a => (a,0)
  | .ask q next =>
    let result := executeActualNP (next (by classical exact decide (encodedQuery q∈cappedPrefixFeasibilityLanguage)))
    (result.1,result.2+1)
end Reference.IV04ConcreteOracleSearch
