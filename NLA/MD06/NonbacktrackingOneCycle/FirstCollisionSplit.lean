module

public import NLA.MD06.NonbacktrackingOneCycle.NoCollision

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_first_collision_split {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2))
    (hs : s.collisions=0) (hw : 0<(ExposureRun p s w).collisions) :
    ∃ u z : List (Fin 2),∃ i : Fin 2,w=u++i::z ∧
      (ExposureRun p s u).collisions=0 ∧
      (ExposureRun p s u).current∉UsedDarts (ExposureRun p s u).exposed ∧
      (p.val (ExposureRun p s u).current).1∈(ExposureRun p s u).visited := by
  induction w generalizing s with
  | nil => exact (by change 0<s.collisions at hw;omega)
  | cons i w ih =>
    by_cases hz : (ExposureStep p s i).collisions=0
    · obtain ⟨u,z,j,hword,hc,hf,hv⟩:=ih (ExposureStep p s i) hz hw
      exact ⟨i::u,z,j,by simp [hword],hc,hf,hv⟩
    · have hhit : s.current∉UsedDarts s.exposed ∧ (p.val s.current).1∈s.visited := by
        by_contra h
        have hh : (ExposureStep p s i).collisions=0 := by simp [ExposureStep,hs,h]
        exact hz hh
      exact ⟨[],w,i,rfl,hs,hhit.1,hhit.2⟩

#print axioms actual_first_collision_split
end Reference.MD06OneCycle
