module

public import NLA.MD06.NonbacktrackingWalkExposure.MeanDefinitions
public import NLA.MD06.NonbacktrackingWalkExposure.WordDefinitions
public import Mathlib.Data.List.OfFn

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def MultipleCollisionWords {n : ℕ} (p : Pairing n) (t : ℕ) : ℕ :=
  ∑ a : Dart n,Fintype.card {w : Fin t→Fin 2 //
    2≤(ExposureRun p (InitialState a) (List.ofFn w)).collisions}

def MeanMultipleCollisionWords (n t : ℕ) : ℝ :=
  PairingMean n (fun p=>(MultipleCollisionWords p t : ℝ))

end Reference.MD06WalkExposure
