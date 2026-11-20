module

public import NLA.MD06.MixedPatternShapes.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedPatternShapes
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
open Reference.MD06Simplicity

def LoopCycle {n : ℕ} (d : LoopDatum n) : CycleData n 1 :=
  ({ toFun := fun _ => d.1
     inj' := fun _ _ _ => Subsingleton.elim _ _ },
    fun _ => ⟨d.2.val,ne_of_lt d.2.property⟩)

def DoubleVertexEmbedding {n : ℕ} (d : DoubleDatum n) : Fin 2↪Fin n :=
  { toFun := fun i => if i=0 then d.1.val.1 else d.1.val.2
    inj' := by
      intro i j h
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (d.1.property.ne (by simpa using h))
      · exact False.elim (d.1.property.ne (by simpa using h.symm))
      · rfl }

def DoubleCycle {n : ℕ} (d : DoubleDatum n) : CycleData n 2 :=
  (DoubleVertexEmbedding d,
    fun i => if i=0 then ⟨(d.2.1.val.2,d.2.1.val.1),ne_of_gt d.2.1.property⟩
      else if d.2.2.2 then
        ⟨(d.2.2.1.val.2,d.2.2.1.val.1),ne_of_gt d.2.2.1.property⟩
      else ⟨d.2.2.1.val,ne_of_lt d.2.2.1.property⟩)

def BadLength {n : ℕ} (d : BadDatum n) : ℕ :=
  match d with
  | .inl _ => 1
  | .inr _ => 2

def BadCycle {n : ℕ} (d : BadDatum n) : CycleData n (BadLength d) :=
  match d with
  | .inl b => LoopCycle b
  | .inr b => DoubleCycle b

end Reference.MD06MixedPatternShapes
