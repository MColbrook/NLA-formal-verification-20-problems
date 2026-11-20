module

public import NLA.IV04.PaperVertexSelectionReference
public import NLA.IV04.PaperSignedWordDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Every actual endpoint pair is checked in row-major order, including the
unselected endpoint. The threshold fields do not enter this predicate. -/
def denseEndpointAll (n : ℕ) : ℕ → ℕ → List (List Bool × List Bool) → Prop
  | _, _, [] => True
  | i, j, (lower,upper)::rows =>
      ((i ≤ j+1 ∧ j ≤ i+1) ∨ (signedWordValue lower=0 ∧ signedWordValue upper=0)) ∧
      denseEndpointAll n (if n ≤ j+1 then i+1 else i) (if n ≤ j+1 then 0 else j+1) rows

def denseEndpointAllDecidable (n i j : ℕ) (rows : List (List Bool × List Bool)) :
    Decidable (denseEndpointAll n i j rows) := by
  induction rows generalizing i j with
  | nil => exact isTrue trivial
  | cons row rows ih =>
    obtain ⟨lower,upper⟩ := row
    change Decidable (_ ∧ _)
    haveI := ih (if n ≤ j+1 then i+1 else i) (if n ≤ j+1 then 0 else j+1)
    infer_instance

instance (n i j : ℕ) (rows : List (List Bool × List Bool)) :
    Decidable (denseEndpointAll n i j rows) := denseEndpointAllDecidable n i j rows

def denseSupportInputCode (n : ℕ) (rows : List (List Bool × List Bool)) (rest : List Bool) : List Bool :=
  Complexity.pair n.bits (endpointWordPairsCode rows rest)

end IV04.Paper.Computational
