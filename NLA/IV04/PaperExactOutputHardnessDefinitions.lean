module

public import NLA.IV04.PaperHullReductionDefinitions
public import NLA.IV04.PaperPartitionMatrixOutputDefinitions
public import NLA.IV04.PaperRationalParserDefinitions
public import NLA.IV04.PaperSignedOrderDefinitions
public import NLA.IV04.Complexitylib.Classes.NP.Reduction

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

/-- The range/hull matrix packet has a fixed zero terminator, with no supplied threshold. -/
def polynomialPartitionOutputQuery (input : List Bool) : List Bool :=
  (canonicalWordCode (polynomialPartitionLayerCount input) ++ polynomialPartitionEndpointTable input) ++
    IV04.Paper.rationalCode 0

def polynomialSATOutputQuery (input : List Bool) : List Bool :=
  polynomialPartitionOutputQuery (polynomialSATPartitionCode input)

def polynomialSATRangeAnswer (input : List Bool) : List Bool :=
  polynomialFractionLe (polynomialPartitionThresholdFraction (polynomialSATPartitionCode (pairFst input)))
    (rationalParserFraction (pairSnd (pairSnd (encodedRationalParser (pairSnd input)))))

def polynomialSATHullAnswer (input : List Bool) : List Bool :=
  polynomialFractionLe (rationalParserFraction (pairSnd input))
    (polynomialPartitionHullThresholdFraction (polynomialSATPartitionCode (pairFst input)))

/-- One literal call to an output task, with polynomial-time bit programs before and after it. -/
def PolynomialOneQueryReduction (L : Set (List Bool))
    (task : List Bool → List Bool → Prop) : Prop :=
  ∃ query : List Bool → List Bool, query ∈ FP ∧
    ∃ finish : List Bool → List Bool, finish ∈ FP ∧
      (∀ input, ∃ answer, task (query input) answer) ∧
      ∀ input answer, task (query input) answer →
        (firstBit (finish (pair input answer)) = true ↔ input ∈ L)

def NPHardOutputTask (task : List Bool → List Bool → Prop) : Prop :=
  ∀ L ∈ NP, PolynomialOneQueryReduction L task

noncomputable section
/-- Two complete rational fields are the actual minimum and maximum determinants. -/
def ExactDeterminantRangeOutput (matrix answer : List Bool) : Prop :=
  ∃ (n : ℕ) (pairs : List (ℚ × ℚ)),
    readMatrixRationals matrix = some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [0],[]) ∧
    pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
    ∃ (lo hi : ℚ) (tail : List Bool),
      IV04.Paper.readRational answer = some (lo,tail) ∧
      IV04.Paper.readRational tail = some (hi,[]) ∧
      IsLeast (Matrix.det '' realDenseIntervalBox n pairs) (lo : ℝ) ∧
      IsGreatest (Matrix.det '' realDenseIntervalBox n pairs) (hi : ℝ)

/-- Exact first lower hull endpoint on the paper's regular, bounded, unit-superdiagonal instances. -/
def ExactFirstHullEndpointOutput (matrix answer : List Bool) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n) (pairs : List (ℚ × ℚ)),
    readMatrixRationals matrix = some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [0],[]) ∧
    pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
    (∀ A ∈ realDenseIntervalBox n pairs, A.det ≠ 0 ∧
      ∀ i j : Fin n, j.val = i.val+1 → A i j = 1) ∧
    (IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)).Nonempty ∧
    Bornology.IsBounded (IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)) ∧
    ∃ q : ℚ, IV04.Paper.readRational answer = some (q,[]) ∧
      IsLeast (IV04.Paper.positiveFirstCoordinates n hn (realDenseIntervalBox n pairs)) (q : ℝ)
end
end IV04.Paper.Computational
