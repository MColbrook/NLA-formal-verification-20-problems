module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual three-mode tensor definitions for main.tex TR04 completion. -/
public import NLA.TR04.RealSVD.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.ThreeModeCompletion
noncomputable section
open Reference.RealSVDPackage
open scoped BigOperators

abbrev ThreeTensor (m n p : ℕ) := Matrix (Fin m) (Fin n × Fin p) ℝ

def secondUnfolding {m n p : ℕ} (A : ThreeTensor m n p) :
    Matrix (Fin m × Fin n) (Fin p) ℝ := fun i j => A i.1 (i.2, j)

def tensorFrobeniusSq {m n p : ℕ} (A : ThreeTensor m n p) : ℝ :=
  ∑ i, ∑ j, A i j ^ 2

def feasibleThree {m n p : ℕ} (A : ThreeTensor m n p) (r1 r2 : ℕ) : Prop :=
  A.rank ≤ r1 ∧ (secondUnfolding A).rank ≤ r2

end
end Reference.ThreeModeCompletion
