module

public import NLA.TR04.OptimalityEquality.CountDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.PaperTensorEquality
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality

abbrev TensorIndex (d : ℕ) (dimensions : Fin (d+1) → ℕ) :=
  (i : Fin (d+1)) → Fin (dimensions i)

abbrev SuffixTensorIndex (d : ℕ) (dimensions : Fin (d+1) → ℕ) :=
  (i : Fin d) → Fin (dimensions i.succ)

/-- Literal first-mode unfolding of a finite dense real tensor. The columns
enumerate the remaining mode indices through a fixed finite equivalence. -/
def actualFirstUnfolding {d : ℕ} (dimensions : Fin (d+1) → ℕ)
    (A : TensorIndex d dimensions → ℝ) :
    Rect (dimensions 0) (Fintype.card (SuffixTensorIndex d dimensions)) :=
  fun row column => A (Fin.cases row
    ((Fintype.equivFin (SuffixTensorIndex d dimensions)).symm column))

end
end Reference.PaperTensorEquality
