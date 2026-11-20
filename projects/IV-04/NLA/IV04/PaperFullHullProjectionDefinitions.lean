module

public import NLA.IV04.PaperExactOutputHardnessDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational

def polynomialFirstHullProjection (answer : List Bool) : List Bool :=
  polynomialFractionOutput (rationalParserFraction answer)

noncomputable section
/-- Complete finite solution-hull output: literal lower/upper rational endpoints for every coordinate. -/
def ExactFullHullOutput (matrix answer : List Bool) : Prop :=
  ∃ (n : ℕ) (hn : 0 < n) (pairs bounds : List (ℚ × ℚ)),
    readMatrixRationals matrix = some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [0],[]) ∧
    pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
    (∀ A ∈ realDenseIntervalBox n pairs, A.det ≠ 0 ∧
      ∀ i j : Fin n, j.val = i.val+1 → A i j = 1) ∧
    (IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)).Nonempty ∧
    Bornology.IsBounded (IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs)) ∧
    bounds.length = n ∧
    answer = bounds.flatMap (fun row => IV04.Paper.rationalCode row.1 ++ IV04.Paper.rationalCode row.2) ∧
    ∀ i : Fin n,
      IsLeast ((fun x : Fin n → ℝ => x i) ''
        IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs))
        ((bounds.getD i.val (0,0)).1 : ℝ) ∧
      IsGreatest ((fun x : Fin n → ℝ => x i) ''
        IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs))
        ((bounds.getD i.val (0,0)).2 : ℝ)
end
end IV04.Paper.Computational
