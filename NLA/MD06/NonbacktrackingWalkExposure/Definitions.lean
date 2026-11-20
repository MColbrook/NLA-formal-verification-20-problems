module

public import NLA.MD06.AdaptiveExposure.Definitions
public import NLA.MD06.NonbacktrackingFoundation.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

structure ExposureState (n : ℕ) where
  current : Dart n
  exposed : Finset (Dart n × Dart n)
  visited : Finset (Fin n)
  collisions : ℕ

def PortChoice {n : ℕ} (a : Dart n) (i : Fin 2) : Dart n :=
  (a.1,⟨(a.2.val+i.val+1)%3,Nat.mod_lt _ (by decide)⟩)

noncomputable def ExposureStep {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2) :
    ExposureState n :=
  let b := p.val s.current
  { current := PortChoice b i
    exposed := if s.current ∉ UsedDarts s.exposed then insert (s.current,b) s.exposed else s.exposed
    visited := insert b.1 s.visited
    collisions := s.collisions + if s.current ∉ UsedDarts s.exposed ∧ b.1 ∈ s.visited then 1 else 0 }

noncomputable def ExposureRun {n : ℕ} (p : Pairing n) : ExposureState n → List (Fin 2) → ExposureState n
  | s,[] => s
  | s,i::w => ExposureRun p (ExposureStep p s i) w

def WalkEnd {n : ℕ} (p : Pairing n) : Dart n → List (Fin 2) → Dart n
  | a,[] => a
  | a,i::w => WalkEnd p (PortChoice (p.val a) i) w

def InitialState {n : ℕ} (a : Dart n) : ExposureState n :=
  {current:=a,exposed:=∅,visited:={a.1},collisions:=0}

end Reference.MD06WalkExposure
