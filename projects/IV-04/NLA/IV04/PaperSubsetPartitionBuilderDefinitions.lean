module

public import NLA.IV04.PaperPayloadNaturalOutputDefinitions
public import NLA.IV04.PaperWordListSumDefinitions
public import NLA.IV04.PaperSATPartitionCodeDefinitions
public import Mathlib.Tactic.FinCases

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational

/-- Input is a count word, target word and a nested list of weight words.
    Every arithmetic and output operation is an actual binary program. -/
def polynomialSubsetPartitionCode (input : List Bool) : List Bool :=
  let count := Complexity.pairFst input
  let target := Complexity.pairFst (Complexity.pairSnd input)
  let weights := Complexity.pairSnd (Complexity.pairSnd input)
  let total := polynomialWordListSum weights
  let first := polynomialWordAdd total (polynomialWordAdd (polynomialWordAdd target target) [true])
  let second := polynomialWordAdd (polynomialWordAdd total total) [true]
  canonicalWordCode (polynomialWordAdd count [false,true]) ++
    polynomialPayloadNaturals weights ++ canonicalWordCode first ++ canonicalWordCode second

def subsetPartitionBuilderInput (n : ℕ) (w : Fin n → ℕ) (target : ℕ) : List Bool :=
  Complexity.pair n.bits (Complexity.pair target.bits
    (payloadListCode ((List.ofFn w).map Nat.bits)))

def subsetPartitionBuilderWeights {n : ℕ} (w : Fin n → ℕ) (target : ℕ) : Fin (n+2) → ℕ :=
  Fin.append w ![(∑ i, w i)+2*target+1,2*(∑ i, w i)+1]

def subsetPartitionBuilderIndex (n : ℕ) : Fin n ⊕ Bool ≃ Fin (n+2) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) SATReduction.boolFinTwo).trans finSumFinEquiv

noncomputable def actualSubsetBuilderPartition (n : ℕ) (w : Fin n → ℕ) (target : ℕ)
    (hw : ∀ i, 0<w i) : IV04.Paper.IntegerPartition where
  m := n+2
  nonempty := by omega
  weight := subsetPartitionBuilderWeights w target
  positive j := by
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa only [subsetPartitionBuilderWeights,Fin.append_left] using hw i
    · intro i
      fin_cases i <;> simp [subsetPartitionBuilderWeights]

end IV04.Paper.Computational
