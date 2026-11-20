module

public import NLA.TR27.PaperProjectionDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.TR27.Paper

def curveTangent (D : ℕ) (t : Option ℂ) : CurveSpace D :=
  match t with
  | some a => fun j => (j.val : ℂ) * a^(j.val-1)
  | none => fun j => if j.val+1 = D then 1 else 0

def infinityChart (D : ℕ) (t : ℂ) : CurveSpace D := fun j => t^(D-j.val)

end NLA.TR27.Paper
