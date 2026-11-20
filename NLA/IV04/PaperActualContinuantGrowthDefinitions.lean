module

public import NLA.IV04.PaperCommonDenominatorDefinitions
public import NLA.IV04.PaperEncodingDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def rationalTableCode {k : ℕ} (q : Fin k → ℚ) : List Bool :=
  naturalCode k ++ (List.ofFn q).flatMap rationalCode

/-- Finite coefficient selection, extended by zero outside the matrix dimension. -/
def selectedRationalCoefficients {n k : ℕ} (q : Fin k → ℚ)
    (selection : Fin n → Fin k) : ℕ → ℚ :=
  fun i => if hi : i < n then q (selection ⟨i,hi⟩) else 0

def selectedIntegerCoefficients {n k : ℕ} (q : Fin k → ℚ)
    (selection : Fin n → Fin k) : ℕ → ℤ :=
  fun i => if hi : i < n then rationalCommonNumerator q (selection ⟨i,hi⟩) else 0

end IV04.Paper.Computational
