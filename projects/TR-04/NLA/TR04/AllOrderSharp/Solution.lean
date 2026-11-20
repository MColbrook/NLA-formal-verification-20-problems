module

public import NLA.TR04.AllOrderSharp.Sharpness

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp.Interface
open Reference.LexTensorCompletion Reference.LexOrderedTensorSolver

theorem fixed_order_strict (q : ℕ) (hq : 0 < q)
    (A Y : Tensor (q+2) (List.replicate (q+1) (q+2)))
    (hY : feasible (q+2) (List.replicate (q+1) (q+2)) Y (ranks q))
    (hpositive : 0 < tensorFrobeniusSq (A-Y)) :
    tensorFrobeniusSq (Sub.sub A (solver A (q+1) (remainingRanks q))) <
      ((q+1 : ℕ) : ℝ) * tensorFrobeniusSq (A-Y) :=
  NLA.TR04.AllOrderSharp.fixed_order_strict q hq A Y hY hpositive

theorem fixed_order_sharp (q : ℕ) (C : ℝ) (hC : C < ((q+1 : ℕ) : ℝ)) :
    ∃ A Y : Tensor (q+2) (List.replicate (q+1) (q+2)),
      feasible (q+2) (List.replicate (q+1) (q+2)) Y (ranks q) ∧
      0 < tensorFrobeniusSq (A-Y) ∧
      C * tensorFrobeniusSq (A-Y) <
        tensorFrobeniusSq (Sub.sub A (solver A (q+1) (remainingRanks q))) :=
  NLA.TR04.AllOrderSharp.fixed_order_sharp q C hC

#print axioms fixed_order_strict
#print axioms fixed_order_sharp

end NLA.TR04.AllOrderSharp.Interface
