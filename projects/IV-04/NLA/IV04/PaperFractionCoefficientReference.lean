module

public import NLA.IV04.PaperFractionCoefficientDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Semantic list reference for the words emitted by the concrete coefficient loop. -/
def coefficientWords : List Bool → List (List Bool) → List (List Bool)
  | _, [] => []
  | prior, fraction :: fractions =>
      clearedFractionWord prior fraction (payloadListCode fractions) ::
        coefficientWords (canonicalWordMultiply prior (Complexity.pairSnd fraction)) fractions

def coefficientFinalPrior : List Bool → List (List Bool) → List Bool
  | prior, [] => prior
  | prior, fraction :: fractions =>
      coefficientFinalPrior (canonicalWordMultiply prior (Complexity.pairSnd fraction)) fractions

def fractionDenominatorProduct (fractions : List (List Bool)) : ℕ :=
  ((fractions.map Complexity.pairSnd).map wordValue).prod

end IV04.Paper.Computational
