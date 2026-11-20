module

public import NLA.MD06.NonbacktrackingOneCycle.SupportNextDefinitions
public import NLA.MD06.NonbacktrackingWalkExposure.MeanDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def PrefixWord {t ell : ℕ} (h : ell≤t) (w : Fin t→Fin 2) : Fin ell→Fin 2 :=
  fun j=>w ⟨j.val,lt_of_lt_of_le j.isLt h⟩

def FirstCycleEvent {n : ℕ} (p : Pairing n) (a : Dart n) (t : ℕ) (w : Fin t→Fin 2) : Prop :=
  0<t ∧ (ExposureRun p (InitialState a) (List.ofFn w)).current=a ∧
    (ExposureRun p (InitialState a) ((List.ofFn w).take (t-1))).collisions=0

def ClosedOneCollisionEvent {n : ℕ} (p : Pairing n) (a : Dart n) (t : ℕ) (w : Fin t→Fin 2) : Prop :=
  (ExposureRun p (InitialState a) (List.ofFn w)).current=a ∧
    (ExposureRun p (InitialState a) (List.ofFn w)).collisions=1

noncomputable def FirstCycleWords {n : ℕ} (p : Pairing n) (t : ℕ) : ℕ :=
  ∑ a : Dart n,Fintype.card {w : Fin t→Fin 2 // FirstCycleEvent p a t w}

noncomputable def MeanFirstCycleWords (n t : ℕ) : ℝ :=
  PairingMean n (fun p=>(FirstCycleWords p t : ℝ))

noncomputable def ClosedOneCollisionWords {n : ℕ} (p : Pairing n) (t : ℕ) : ℕ :=
  ∑ a : Dart n,Fintype.card {w : Fin t→Fin 2 // ClosedOneCollisionEvent p a t w}

noncomputable def MeanClosedOneCollisionWords (n t : ℕ) : ℝ :=
  PairingMean n (fun p=>(ClosedOneCollisionWords p t : ℝ))

end Reference.MD06OneCycle
