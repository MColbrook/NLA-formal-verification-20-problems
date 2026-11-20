module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual above-boundary multiplicity for main.tex lem:tr04-equality. -/
public import NLA.TR04.OptimalityEquality.MultiplicityDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage

def aboveMultiplicity {m n : ℕ} (A : Rect m n) (tau : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => tau < singularValue A.transpose i.val)).card

end
end Reference.RealOptimalityEquality
