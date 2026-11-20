module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Explicit ascending original-index scans and inverse lookup; no choice of enumeration.
Apache2 attribution: George Stepaniants 2026; new formalization by Codex. -/
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Card

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedIndex

theorem indexEnum_inverse_lookup {m : ℕ} (p : Fin m → Prop) [DecidablePred p]
    (j : Fin (Fintype.card {i : Fin m // p i})) :
    ((indexEnum p).symm j).val=(indexList p).get ((finCongr (indexList_length p)).symm j) := rfl

theorem indexEnum_forward_lookup {m : ℕ} (p : Fin m → Prop) [DecidablePred p]
    (i : {i : Fin m // p i}) : (indexEnum p i).val=(indexList p).idxOf i.val := rfl

end Reference.LexOrderedIndex
