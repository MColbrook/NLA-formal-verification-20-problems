module

public import NLA.IV04.Complexitylib.SAT.Encoding
public import NLA.IV04.PaperPositionalDigitDefinitions

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction
open Complexity.SAT

def satVariables (φ : CNF) : ℕ := φ.maxVar + 1

def satLiteralBudget (φ : CNF) : ℕ := φ.flatten.length + 1

def satClauseTarget (φ : CNF) : ℕ := satVariables φ * satLiteralBudget φ

def satDigitBase (φ : CNF) : ℕ := 4 * satClauseTarget φ + 3

def satClause (φ : CNF) (j : Fin φ.length) : Clause := φ[j]

def literalCount (c : Clause) (v : ℕ) (b : Bool) : ℕ :=
  (c.map (fun ℓ => if ℓ.var = v ∧ ℓ.sign = b then 1 else 0)).sum

def trueLiteralCount (c : Clause) (a : ℕ → Bool) : ℕ :=
  (c.map (fun ℓ => if a ℓ.var = ℓ.sign then 1 else 0)).sum

abbrev SATDigit (φ : CNF) := Fin (satVariables φ) ⊕ Fin φ.length

abbrev SATSlot (φ : CNF) :=
  (Fin (satVariables φ) × Bool) ⊕ (Fin φ.length × Fin (satClauseTarget φ - 1))

/-- Literal variable markers, matching-literal clause digits, and unit slack digits. -/
def satWeightDigits (φ : CNF) : SATSlot φ → SATDigit φ → ℕ
  | Sum.inl (v,b), Sum.inl u => if v = u then 1 else 0
  | Sum.inl (v,b), Sum.inr j => literalCount (satClause φ j) v.val b
  | Sum.inr (j,k), Sum.inl v => 0
  | Sum.inr (j,k), Sum.inr l => if j = l then 1 else 0

def satTargetDigits (φ : CNF) : SATDigit φ → ℕ
  | Sum.inl _ => 1
  | Sum.inr _ => satClauseTarget φ

/-- The sum-index equivalence has the concrete offsets v and V+j. -/
def satDigitValue (φ : CNF) (d : SATDigit φ → ℕ) : ℕ :=
  positionalValue (satDigitBase φ) (fun k => d (finSumFinEquiv.symm k))

def satSubsetWeights (φ : CNF) (i : SATSlot φ) : ℕ :=
  satDigitValue φ (satWeightDigits φ i)

def satSubsetTarget (φ : CNF) : ℕ := satDigitValue φ (satTargetDigits φ)

/-- Actual coordinatewise sum of the selected literal weight vectors. -/
def satSelectedDigits (φ : CNF) (selected : SATSlot φ → Bool) : SATDigit φ → ℕ :=
  fun j => ∑ i, if selected i then satWeightDigits φ i j else 0
end IV04.Paper.Computational.SATReduction