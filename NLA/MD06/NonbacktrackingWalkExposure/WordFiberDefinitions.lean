module

public import NLA.MD06.NonbacktrackingWalkExposure.WordDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06Nonbacktracking
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def WordFiberSplit {n : ℕ} (p : Pairing n) (t : ℕ) (a b : Dart n) :
    {w : Fin (t+1) → Fin 2 // WordRun p a (t+1) w=b} ≃
      Σ i : Fin 2, {w : Fin t → Fin 2 // WordRun p (PortChoice (p.val a) i) t w=b} where
  toFun w := ⟨w.val 0,⟨fun i => w.val i.succ,w.property⟩⟩
  invFun w := ⟨(Fin.cases (motive := fun _ : Fin (t+1) => Fin 2) w.1 w.2.val), by
    simpa only [WordRun,Fin.cases_zero,Fin.cases_succ] using w.2.property⟩
  left_inv := by
    intro w
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j;rfl
  right_inv := by
    rintro ⟨i,⟨w,hw⟩⟩
    rfl

end Reference.MD06WalkExposure
