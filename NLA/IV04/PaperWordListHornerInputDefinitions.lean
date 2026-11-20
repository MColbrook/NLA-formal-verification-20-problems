module

public import NLA.IV04.PaperWordListHornerDefinitions
public import NLA.IV04.PaperSATDigitDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def positionalDigitPayloads {n : ℕ} (d : Fin n → ℕ) : List (List Bool) :=
  (List.ofFn d).reverse.map Nat.bits

def encodedPositionalDigits (b n : ℕ) (d : Fin n → ℕ) : List Bool :=
  Complexity.pair b.bits (payloadListCode (positionalDigitPayloads d))

def actualSATWeightHornerInput (φ : Complexity.SAT.CNF) (i : SATReduction.SATSlot φ) : List Bool :=
  encodedPositionalDigits (SATReduction.satDigitBase φ) (SATReduction.satVariables φ+φ.length)
    (fun k => SATReduction.satWeightDigits φ i (finSumFinEquiv.symm k))

def actualSATTargetHornerInput (φ : Complexity.SAT.CNF) : List Bool :=
  encodedPositionalDigits (SATReduction.satDigitBase φ) (SATReduction.satVariables φ+φ.length)
    (fun k => SATReduction.satTargetDigits φ (finSumFinEquiv.symm k))

end IV04.Paper.Computational