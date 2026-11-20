module

public import NLA.IV04.PaperMatrixDenseSupportDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def rationalDenseEndpointAll (n : ℕ) : ℕ → ℕ → List (ℚ × ℚ) → Prop
  | _, _, [] => True
  | i, j, (lower,upper)::rows =>
      ((i ≤ j+1 ∧ j ≤ i+1) ∨ (lower=0 ∧ upper=0)) ∧
      rationalDenseEndpointAll n (if n ≤ j+1 then i+1 else i) (if n ≤ j+1 then 0 else j+1) rows

instance (n i j : ℕ) (rows : List (ℚ × ℚ)) : Decidable (rationalDenseEndpointAll n i j rows) := by
  induction rows generalizing i j with
  | nil => exact isTrue trivial
  | cons row rows ih =>
    obtain ⟨lower,upper⟩ := row
    change Decidable (_ ∧ _)
    haveI := ih (if n ≤ j+1 then i+1 else i) (if n ≤ j+1 then 0 else j+1)
    infer_instance

end IV04.Paper.Computational
