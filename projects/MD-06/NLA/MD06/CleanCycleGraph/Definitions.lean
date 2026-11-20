module

public import NLA.MD06.CycleProfile.RootDefinitions
public import NLA.MD06.QuantitativeCorrection.GradientDefinitions
public import NLA.MD06.LaplacianSpectralGap.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06CycleProfile

abbrev LevelNodes (ell j : ℕ) := Fin ell × Fin (2^(j-1))
abbrev TreeNodes (ell R : ℕ) := (j : Fin (R+1)) × LevelNodes ell j.val

def RootSign {ell : ℕ} (i : Fin ell) : ℝ := if i.val % 4 < 2 then 1 else -1

def NodeProfile {ell R : ℕ} (x : TreeNodes ell R) : ℝ :=
  RootSign x.2.1 * Height R (Root R) x.1.val

def LeafResidual {ell R : ℕ} (x : LevelNodes ell R) : ℝ :=
  -RootSign x.1 * Root R / (2 : ℝ)^(R-1)
end Reference.MD06CleanCycle
