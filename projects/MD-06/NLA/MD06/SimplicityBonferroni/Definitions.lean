module

public import NLA.MD06.PatternUnions.Definitions
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Simplicity
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts

abbrev OrderedLocalPair := {ab : Fin 3 × Fin 3 // ab.1 < ab.2}
abbrev LoopDatum (n : ℕ) := Fin n × OrderedLocalPair
abbrev DoubleDatum (n : ℕ) :=
  {uv : Fin n × Fin n // uv.1 < uv.2} × OrderedLocalPair × OrderedLocalPair × Bool
abbrev BadDatum (n : ℕ) := LoopDatum n ⊕ DoubleDatum n

def LoopPattern {n : ℕ} (d : LoopDatum n) : Finset (Dart n × Dart n) :=
  {((d.1,d.2.val.1),(d.1,d.2.val.2))}

def DoublePattern {n : ℕ} (d : DoubleDatum n) : Finset (Dart n × Dart n) :=
  if d.2.2.2 then
    {((d.1.val.1,d.2.1.val.1),(d.1.val.2,d.2.2.1.val.2)),
     ((d.1.val.1,d.2.1.val.2),(d.1.val.2,d.2.2.1.val.1))}
  else
    {((d.1.val.1,d.2.1.val.1),(d.1.val.2,d.2.2.1.val.1)),
     ((d.1.val.1,d.2.1.val.2),(d.1.val.2,d.2.2.1.val.2))}

def BadPattern {n : ℕ} (d : BadDatum n) : Finset (Dart n × Dart n) :=
  match d with
  | .inl x => LoopPattern x
  | .inr x => DoublePattern x

attribute [local instance] Classical.propDecidable

noncomputable def BadCount {n : ℕ} (p : Pairing n) : ℕ :=
  Fintype.card {d : BadDatum n // Matches (BadPattern d) p}

end Reference.MD06Simplicity