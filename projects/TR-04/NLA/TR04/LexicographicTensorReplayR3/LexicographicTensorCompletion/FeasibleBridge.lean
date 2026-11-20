module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Concrete recursion defines exactly the actual manuscript feasible set. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorCompletion.RankPreservation
public import NLA.TR04.LexicographicFeasibilityBridge.Layout

@[expose] public section
set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
theorem feasible_iff_feasibleLex {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (rs : List ℕ) :
    feasible m ns A rs ↔ Reference.LexicographicFeasibilityBridge.feasibleLex m ns A rs := by
  induction ns generalizing m rs with
  | nil => simp only [feasible,Reference.LexicographicFeasibilityBridge.feasibleLex]
  | cons n ns ih =>
      cases rs with
      | nil => simp only [feasible,Reference.LexicographicFeasibilityBridge.feasibleLex]
      | cons r rs =>
          simp only [feasible,Reference.LexicographicFeasibilityBridge.feasibleLex]
          have hm : merge A=Reference.LexicographicFeasibilityBridge.mergeLex A := rfl
          rw [← hm]
          exact and_congr Iff.rfl (ih (merge A) rs)
theorem feasible_iff_original {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (rs : List ℕ) :
    feasible m ns A rs ↔ Reference.RecursiveTensorCompletion.feasible m ns A rs :=
  (feasible_iff_feasibleLex A rs).trans (Reference.LexicographicFeasibilityBridge.feasibleLex_iff_feasible A rs)
#print axioms feasible_iff_original
end
end Reference.LexTensorCompletion
