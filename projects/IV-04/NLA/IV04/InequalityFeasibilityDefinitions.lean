module

public import NLA.IV04.InequalityVerifierDefinitions
public import NLA.IV04.Complexitylib.Classes.NP
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational
open scoped Matrix
namespace IV04.Paper.InequalityFeasibility

def integerRealFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℝ) : Prop := ∀ i, (∑ j, (A i j : ℝ)*x j)≤(b i : ℝ)

def wordMatrixRowCode {m n : ℕ} (A : Matrix (Fin m) (Fin n) (List Bool))
    (b : Fin m → List Bool) (i : Fin m) : List Bool :=
  pair (payloadListCode (List.ofFn (A i))) (b i)

def wordMatrixInstanceCode {m n : ℕ} (A : Matrix (Fin m) (Fin n) (List Bool))
    (b : Fin m → List Bool) : List Bool := payloadListCode (List.ofFn (wordMatrixRowCode A b))

def wordMatrixValue {m n : ℕ} (A : Matrix (Fin m) (Fin n) (List Bool)) :
    Matrix (Fin m) (Fin n) ℤ := fun i j => signedWordValue (A i j)

def wordVectorValue {m : ℕ} (b : Fin m → List Bool) : Fin m → ℤ :=
  fun i => signedWordValue (b i)

def integerFeasibilityLanguage : Language := {inputCode | ∃ m n : ℕ,
  ∃ A : Matrix (Fin m) (Fin n) (List Bool), ∃ b : Fin m → List Bool,
    inputCode=wordMatrixInstanceCode A b ∧
    ∃ x, integerRealFeasible (wordMatrixValue A) (wordVectorValue b) x}

def canonicalIntegerMatrixInstanceCode {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) : List Bool := payloadListCode (List.ofFn (fun i =>
      pair (payloadListCode ((List.ofFn (A i)).map InequalityVerifier.inequalityIntegerWord))
        (InequalityVerifier.inequalityIntegerWord (b i))))

def inequalityInstanceLengthPolynomial (N : ℕ) : ℕ := (4*N+1)*(5*N*N+3)

noncomputable def certificateLengthPolynomial : Polynomial ℕ :=
  (Polynomial.C 4*Polynomial.X+Polynomial.C 1)*
    (Polynomial.C 5*Polynomial.X*Polynomial.X+Polynomial.C 3)

def certificateRuler (inputCode : List Bool) : List Bool :=
  List.replicate (inequalityInstanceLengthPolynomial inputCode.length) true

def boundedInequalityVerifier (input : List Bool) : List Bool :=
  andBit (InequalityVerifier.polynomialInequalitySystemVerifier input)
    (InequalityVerifier.EqualityFlags.lenLeFlag (certificateRuler (pairFst input)) (pairSnd input))

def boundedInequalityVerifierLanguage : Language :=
  {input | boundedInequalityVerifier input=[true]}

def prefixFeasibilityLanguage : Language := {query | ∃ inputCode initialBits : List Bool,
  query=pair inputCode initialBits ∧ ∃ tail : List Bool,
    (initialBits++tail).length≤ inequalityInstanceLengthPolynomial inputCode.length ∧
    InequalityVerifier.polynomialInequalitySystemVerifier (pair inputCode (initialBits++tail))=[true]}

def prefixInequalityVerifier (input : List Bool) : List Bool :=
  andBit (InequalityVerifier.EqualityFlags.eqFlag (pairFst input)
    (pair (pairFst (pairFst input)) (pairSnd (pairFst input))))
    (boundedInequalityVerifier (pair (pairFst (pairFst input))
      (pairSnd (pairFst input)++pairSnd input)))

def prefixInequalityVerifierLanguage : Language :=
  {input | prefixInequalityVerifier input=[true]}
def cappedPrefixFeasibilityLanguage : Language := {query | ∃ inputCode ruler initialBits : List Bool,
  query=pair inputCode (pair ruler initialBits) ∧ ∃ tail : List Bool,
    (initialBits++tail).length≤ruler.length ∧
    (initialBits++tail).length≤ inequalityInstanceLengthPolynomial inputCode.length ∧
    InequalityVerifier.polynomialInequalitySystemVerifier (pair inputCode (initialBits++tail))=[true]}

def cappedPrefixInequalityVerifier (input : List Bool) : List Bool :=
  andBit (InequalityVerifier.EqualityFlags.eqFlag (pairFst input)
    (pair (pairFst (pairFst input))
      (pair (pairFst (pairSnd (pairFst input))) (pairSnd (pairSnd (pairFst input))))))
    (andBit (InequalityVerifier.EqualityFlags.lenLeFlag (pairFst (pairSnd (pairFst input)))
      (pairSnd (pairSnd (pairFst input))++pairSnd input))
      (boundedInequalityVerifier (pair (pairFst (pairFst input))
        (pairSnd (pairSnd (pairFst input))++pairSnd input))))

def cappedPrefixInequalityVerifierLanguage : Language :=
  {input | cappedPrefixInequalityVerifier input=[true]}

end IV04.Paper.InequalityFeasibility
