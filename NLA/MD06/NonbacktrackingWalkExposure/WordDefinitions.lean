module

public import NLA.MD06.NonbacktrackingWalkExposure.Definitions
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def WordRun {n : ℕ} (p : Pairing n) : Dart n → (t : ℕ) → (Fin t → Fin 2) → Dart n
  | a,0,_ => a
  | a,t+1,w => WordRun p (PortChoice (p.val a) (w 0)) t (fun i => w i.succ)

noncomputable def WordCount {n : ℕ} (p : Pairing n) (t : ℕ) (a b : Dart n) : ℕ :=
  Fintype.card {w : Fin t → Fin 2 // WordRun p a t w=b}

noncomputable def ClosedWordCount {n : ℕ} (p : Pairing n) (t : ℕ) : ℕ :=
  ∑ a : Dart n, WordCount p t a a

end Reference.MD06WalkExposure
