module

public import NLA.TR04.ThreeModeCompletion.Completion
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.ThreeModeCompletion
open Reference.RealSVDPackage

theorem verified_three_mode_completion {m n p k : ℕ}
    (A : ThreeTensor m n p) (U : Rect m k) (hU : U.transpose * U = 1)
    (r1 r2 : ℕ) (hk : k ≤ r1) :
    ∃ X : ThreeTensor m n p, feasibleThree X r1 r2 ∧
      ∀ Y : ThreeTensor m n p, feasibleThree Y r1 r2 →
        tensorFrobeniusSq (A-X) ≤ tensorFrobeniusSq (A-U*U.transpose*A) +
          tensorFrobeniusSq (U.transpose*(A-Y)) ∧
        tensorFrobeniusSq (A-X) ≤ tensorFrobeniusSq (A-U*U.transpose*A) +
          tensorFrobeniusSq (U*U.transpose*(A-Y)) := by
  exact three_mode_completion A U hU r1 r2 hk

#print axioms verified_three_mode_completion
end Reference.ThreeModeCompletion
