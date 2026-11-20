module

public import NLA.IV04.PaperIntegerContinuantMachineDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def integerContinuantWordRun : List (List Bool) → List Bool → List Bool → List Bool × List Bool
  | [], previous, before => (previous,before)
  | row :: rows, previous, before =>
      integerContinuantWordRun rows (integerContinuantNext row previous before) previous

def integerContinuantRowValue (row : List Bool) : ℤ × ℤ × ℤ :=
  (signedWordValue (Complexity.pairFst row),
    signedWordValue (Complexity.pairFst (Complexity.pairSnd row)),
    signedWordValue (Complexity.pairSnd (Complexity.pairSnd row)))

def integerContinuantNumericRun : List (ℤ × ℤ × ℤ) → ℤ → ℤ → ℤ × ℤ
  | [], previous, before => (previous,before)
  | row :: rows, previous, before =>
      integerContinuantNumericRun rows (row.1*previous-row.2.1*row.2.2*before) previous

def integerContinuantNumericRows (a lower upper : ℕ → ℤ) (n : ℕ) : List (ℤ × ℤ × ℤ) :=
  (List.range n).map (fun i => (a i,lower i,upper (i-1)))

def integerSignedWord (value : ℤ) : List Bool := decide (value < 0) :: value.natAbs.bits

def integerContinuantRowCode (row : ℤ × ℤ × ℤ) : List Bool :=
  integerContinuantRow (integerSignedWord row.1) (integerSignedWord row.2.1) (integerSignedWord row.2.2)

def integerContinuantRowsCode (a lower upper : ℕ → ℤ) (n : ℕ) : List Bool :=
  payloadListCode ((integerContinuantNumericRows a lower upper n).map integerContinuantRowCode)

end IV04.Paper.Computational
