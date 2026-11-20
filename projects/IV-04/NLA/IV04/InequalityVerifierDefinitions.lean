module

public import NLA.IV04.PaperSignedOrderDefinitions
public import NLA.IV04.PaperPayloadCountDefinitions
public import NLA.IV04.Complexitylib.Classes.P.Defs

@[expose] public section
set_option autoImplicit false
open Complexity IV04.Paper.Computational
namespace IV04.Paper.InequalityVerifier
namespace EqualityFlags

def lenLeFlag (a b : List Bool) : List Bool := notBit (nonemptyFlag (b.drop a.length))
def lenEqFlag (a b : List Bool) : List Bool := andBit (lenLeFlag a b) (lenLeFlag b a)
def xorSuffix : List Bool → List Bool → List Bool
  | [], _ => []
  | true :: x, b =>
      caseBit₀ (notBit (bitAt (b.drop (false :: x).length) b))
        (true :: xorSuffix x b) (false :: xorSuffix x b)
  | false :: x, b =>
      caseBit₀ (bitAt (b.drop (false :: x).length) b)
        (true :: xorSuffix x b) (false :: xorSuffix x b)
def allZeroFlag : List Bool → List Bool
  | [] => [true]
  | true :: _ => [false]
  | false :: x => allZeroFlag x
def eqFlag (a b : List Bool) : List Bool := andBit (lenEqFlag a b) (allZeroFlag (xorSuffix a b))
end EqualityFlags

def signedDotPack (left right total : List Bool) : List Bool := pair left (pair right total)

def signedDotStep (state : List Bool) : List Bool :=
  let left := pairFst state
  let right := pairFst (pairSnd state)
  let total := pairSnd (pairSnd state)
  caseBit₀ (nonemptyFlag left)
    (signedDotPack (pairSnd left) (pairSnd right)
      (polynomialSignedAdd total (polynomialSignedMultiply (pairFst left) (pairFst right)))) state

def signedDotState (input : List Bool) : List Bool :=
  (signedDotStep^[input.length]) (signedDotPack (pairFst input) (pairSnd input) [false])

def polynomialSignedDot (input : List Bool) : List Bool := pairSnd (pairSnd (signedDotState input))

def signedPayloadDot : List (List Bool) → List (List Bool) → ℤ
  | a::as, p::ps => signedWordValue a*signedWordValue p+signedPayloadDot as ps
  | _,_ => 0

def payloadSyntaxStep (state : List Bool) : List Bool :=
  let rest := pairFst state
  let valid := pairSnd state
  caseBit₀ (nonemptyFlag rest)
    (pair (pairSnd rest) (andBit valid (EqualityFlags.eqFlag (pair (pairFst rest) (pairSnd rest)) rest))) state

def payloadSyntaxState (input : List Bool) : List Bool :=
  (payloadSyntaxStep^[input.length]) (pair input [true])

def payloadSyntaxVerdict (state : List Bool) : List Bool :=
  andBit (pairSnd state) (EqualityFlags.eqFlag (pairFst state) [])

def polynomialPayloadSyntax (input : List Bool) : List Bool := payloadSyntaxVerdict (payloadSyntaxState input)

def inequalityRowPack (coefficients bound numerators denominator : List Bool) : List Bool :=
  pair coefficients (pair bound (pair numerators denominator))

def inequalityRowCode (coefficients : List (List Bool)) (bound : List Bool)
    (numerators : List (List Bool)) (denominator : List Bool) : List Bool :=
  inequalityRowPack (payloadListCode coefficients) bound (payloadListCode numerators) denominator

def inequalityRowCoefficients (input : List Bool) : List Bool := pairFst input

def inequalityRowBound (input : List Bool) : List Bool := pairFst (pairSnd input)

def inequalityRowNumerators (input : List Bool) : List Bool := pairFst (pairSnd (pairSnd input))

def inequalityRowDenominator (input : List Bool) : List Bool := pairSnd (pairSnd (pairSnd input))

def inequalityRowRepack (input : List Bool) : List Bool :=
  inequalityRowPack (inequalityRowCoefficients input) (inequalityRowBound input)
    (inequalityRowNumerators input) (inequalityRowDenominator input)

def inequalityRowArithmetic (input : List Bool) : List Bool :=
  polynomialSignedLe
    (polynomialSignedDot (pair (inequalityRowCoefficients input) (inequalityRowNumerators input)))
    (polynomialSignedMultiply (inequalityRowBound input) (false::inequalityRowDenominator input))

def polynomialInequalityRowVerifier (input : List Bool) : List Bool :=
  andBit (EqualityFlags.eqFlag (inequalityRowRepack input) input)
    (andBit (polynomialPayloadSyntax (inequalityRowCoefficients input))
      (andBit (polynomialPayloadSyntax (inequalityRowNumerators input))
        (andBit (EqualityFlags.eqFlag (polynomialPayloadCount (inequalityRowCoefficients input))
            (polynomialPayloadCount (inequalityRowNumerators input)))
          (andBit (polynomialWordLe [true] (inequalityRowDenominator input)) (inequalityRowArithmetic input)))))

def inequalityRowAccepts (input : List Bool) : Prop :=
  ∃ (coefficients numerators : List (List Bool)) (bound denominator : List Bool),
    input=inequalityRowCode coefficients bound numerators denominator ∧
    coefficients.length=numerators.length ∧ 0<wordValue denominator ∧
    signedPayloadDot coefficients numerators ≤ signedWordValue bound*(wordValue denominator : ℤ)

def inequalityRowAt (input : List Bool) : List Bool :=
  let query := pairFst input
  let row := pairSnd input
  andBit (EqualityFlags.eqFlag (pair (pairFst row) (pairSnd row)) row)
    (polynomialInequalityRowVerifier
      (inequalityRowPack (pairFst row) (pairSnd row) (pairFst query) (pairSnd query)))

def inequalityRowsPack (rest query valid : List Bool) : List Bool := pair rest (pair query valid)

def inequalityRowsStep (state : List Bool) : List Bool :=
  let rest := pairFst state
  let query := pairFst (pairSnd state)
  let valid := pairSnd (pairSnd state)
  caseBit₀ (nonemptyFlag rest)
    (inequalityRowsPack (pairSnd rest) query
      (andBit valid (andBit (EqualityFlags.eqFlag (pair (pairFst rest) (pairSnd rest)) rest)
        (inequalityRowAt (pair query (pairFst rest)))))) state

def inequalityRowsState (input : List Bool) : List Bool :=
  (inequalityRowsStep^[input.length]) (inequalityRowsPack (pairFst input) (pairSnd input) [true])

def inequalityRowsVerdict (state : List Bool) : List Bool :=
  andBit (pairSnd (pairSnd state)) (EqualityFlags.eqFlag (pairFst state) [])

def inequalitySystemRepack (input : List Bool) : List Bool :=
  pair (pairFst input) (pair (pairFst (pairSnd input)) (pairSnd (pairSnd input)))

def polynomialInequalitySystemVerifier (input : List Bool) : List Bool :=
  andBit (EqualityFlags.eqFlag (inequalitySystemRepack input) input)
    (andBit (polynomialPayloadSyntax (pairFst (pairSnd input)))
      (andBit (polynomialWordLe [true] (pairSnd (pairSnd input)))
        (inequalityRowsVerdict (inequalityRowsState input))))

def decodedInequalityRow (numerators : List (List Bool)) (denominator row : List Bool) : Prop :=
  ∃ (coefficients : List (List Bool)) (bound : List Bool),
    row=pair (payloadListCode coefficients) bound ∧ coefficients.length=numerators.length ∧
      signedPayloadDot coefficients numerators ≤ signedWordValue bound*(wordValue denominator : ℤ)

def inequalitySystemCode (rows : List (List Bool)) (numerators : List (List Bool)) (denominator : List Bool) : List Bool :=
  pair (payloadListCode rows) (pair (payloadListCode numerators) denominator)

def inequalitySystemAccepts (input : List Bool) : Prop :=
  ∃ (rows numerators : List (List Bool)) (denominator : List Bool),
    input=inequalitySystemCode rows numerators denominator ∧ 0<wordValue denominator ∧
      ∀ row ∈ rows, decodedInequalityRow numerators denominator row

def inequalityTypedSystemCode (rows : List (List (List Bool) × List Bool))
    (numerators : List (List Bool)) (denominator : List Bool) : List Bool :=
  inequalitySystemCode (rows.map (fun row => pair (payloadListCode row.1) row.2)) numerators denominator

def inequalityIntegerWord (z : ℤ) : List Bool := decide (z<0) :: z.natAbs.bits

def inequalityIntegerDot : List ℤ → List ℤ → ℤ
  | a::as,p::ps => a*p+inequalityIntegerDot as ps
  | _,_ => 0

def inequalityIntegerSystemCode (rows : List (List ℤ × ℤ)) (numerators : List ℤ) (denominator : ℕ) : List Bool :=
  inequalityTypedSystemCode (rows.map (fun row => (row.1.map inequalityIntegerWord,inequalityIntegerWord row.2)))
    (numerators.map inequalityIntegerWord) denominator.bits

end IV04.Paper.InequalityVerifier
