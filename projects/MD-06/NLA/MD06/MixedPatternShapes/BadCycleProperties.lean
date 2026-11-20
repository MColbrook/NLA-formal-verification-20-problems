module

public import NLA.MD06.MixedPatternShapes.BadCycleDefinitions
public import NLA.MD06.CanonicalCyclePatterns.Normalization

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedPatternShapes
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
open Reference.MD06Simplicity Reference.MD06BadOverlap Reference.MD06BadJointMoments
attribute [local instance] Classical.propDecidable

theorem actual_loop_canonical_cycle {n : ℕ} (d : LoopDatum n) :
    CanonicalCyclePattern (LoopCycle d)=LoopPattern d := by
  simp [CanonicalCyclePattern,CanonicalConstraints,CyclePattern,LoopCycle,
    cycleEdge,outgoing,incoming,LoopPattern,OrientedEdge,DartLT,
    not_lt_of_gt d.2.property]
  rfl

theorem actual_double_canonical_cycle {n : ℕ} (d : DoubleDatum n) :
    CanonicalCyclePattern (DoubleCycle d)=DoublePattern d := by
  have hv0 : DoubleVertexEmbedding d (0 : Fin 2)=d.1.val.1 := by rfl
  have hv1 : DoubleVertexEmbedding d (1 : Fin 2)=d.1.val.2 := by rfl
  have hr0 : finRotate 2 (0 : Fin 2)=1 := by decide
  have hr1 : finRotate 2 (1 : Fin 2)=0 := by decide
  have hc : CyclePattern (DoubleCycle d)=
      {cycleEdge (DoubleCycle d) 0,cycleEdge (DoubleCycle d) 1} := by
    ext e
    simp only [CyclePattern,Finset.mem_image,Finset.mem_univ,true_and,
      Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨i,hi⟩
      fin_cases i
      · exact Or.inl hi.symm
      · exact Or.inr hi.symm
    · rintro (h | h)
      · exact ⟨0,h.symm⟩
      · exact ⟨1,h.symm⟩
  rw [CanonicalCyclePattern,hc]
  cases hb : d.2.2.2 <;>
    simp [CanonicalConstraints,DoubleCycle,cycleEdge,outgoing,incoming,
      hv0,hv1,hr0,hr1,DoublePattern,hb,OrientedEdge,DartLT,d.1.property,
      not_lt_of_gt d.1.property,ne_of_gt d.1.property]

theorem actual_bad_canonical_cycle {n : ℕ} (d : BadDatum n) :
    CanonicalCyclePattern (BadCycle d)=BadPattern d := by
  cases d with
  | inl b => exact actual_loop_canonical_cycle b
  | inr b => exact actual_double_canonical_cycle b

theorem actual_bad_length_bounds {n : ℕ} (d : BadDatum n) :
    1≤BadLength d ∧ BadLength d≤2 := by
  cases d <;> simp [BadLength]

#print axioms actual_loop_canonical_cycle
#print axioms actual_double_canonical_cycle
#print axioms actual_bad_canonical_cycle
#print axioms actual_bad_length_bounds
end Reference.MD06MixedPatternShapes
