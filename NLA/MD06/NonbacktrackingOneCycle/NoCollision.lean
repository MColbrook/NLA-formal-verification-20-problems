module

public import NLA.MD06.NonbacktrackingOneCycle.DegreeTwo

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_step_collision_mono {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2) :
    s.collisions≤(ExposureStep p s i).collisions := by
  simp only [ExposureStep]
  omega

theorem actual_run_collision_mono {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2)) :
    s.collisions≤(ExposureRun p s w).collisions := by
  induction w generalizing s with
  | nil => exact le_refl _
  | cons i w ih => exact le_trans (actual_step_collision_mono p s i) (ih (ExposureStep p s i))

theorem actual_used_insert_pair {n : ℕ} (C : Finset (Dart n × Dart n)) (a b : Dart n) :
    UsedDarts (insert (a,b) C)=insert a (insert b (UsedDarts C)) := by
  ext d
  simp [UsedDarts]

theorem actual_fresh_new_step_current_unused {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (hc : s.current.1∈s.visited) (hu : ∀ a∈UsedDarts s.exposed,a.1∈s.visited)
    (hf : s.current∉UsedDarts s.exposed) (hn : (p.val s.current).1∉s.visited) :
    (ExposureStep p s i).current∉UsedDarts (ExposureStep p s i).exposed := by
  intro h
  have hh : PortChoice (p.val s.current) i∈insert s.current (insert (p.val s.current) (UsedDarts s.exposed)) := by
    simpa only [ExposureStep,if_pos hf,actual_used_insert_pair] using h
  rcases Finset.mem_insert.mp hh with hh | hh
  · have he:=congrArg (fun a : Dart n=>a.1) hh
    rw [actual_port_choice_fst] at he
    exact hn (he ▸ hc)
  · rcases Finset.mem_insert.mp hh with hh | hh
    · exact actual_port_choice_ne (p.val s.current) i hh
    · exact hn (by simpa only [actual_port_choice_fst] using hu _ hh)

theorem actual_zero_collision_run_unused {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2))
    (hc : s.current.1∈s.visited) (hu : ∀ a∈UsedDarts s.exposed,a.1∈s.visited)
    (hf : s.current∉UsedDarts s.exposed)
    (hz : (ExposureRun p s w).collisions=s.collisions) :
    (ExposureRun p s w).current∉UsedDarts (ExposureRun p s w).exposed := by
  induction w generalizing s with
  | nil => exact hf
  | cons i w ih =>
    have hmon:=actual_run_collision_mono p (ExposureStep p s i) w
    have hstep : (ExposureStep p s i).collisions=s.collisions := by
      have hlow:=actual_step_collision_mono p s i
      change (ExposureRun p (ExposureStep p s i) w).collisions=s.collisions at hz
      omega
    have hn : (p.val s.current).1∉s.visited := by
      intro hn
      have hh : (ExposureStep p s i).collisions=s.collisions+1 := by simp [ExposureStep,hf,hn]
      omega
    apply ih (ExposureStep p s i) (actual_step_current_visited p s i)
      (actual_step_used_visited p s i hc hu)
      (actual_fresh_new_step_current_unused p s i hc hu hf hn)
    exact hz.trans hstep.symm

theorem actual_initial_zero_collision_unused {n : ℕ} (p : Pairing n) (a : Dart n) (w : List (Fin 2))
    (hz : (ExposureRun p (InitialState a) w).collisions=0) :
    (ExposureRun p (InitialState a) w).current∉UsedDarts (ExposureRun p (InitialState a) w).exposed := by
  apply actual_zero_collision_run_unused p (InitialState a) w
  · exact Finset.mem_singleton_self _
  · simp [InitialState,UsedDarts]
  · simp [InitialState,UsedDarts]
  · exact hz

#print axioms actual_step_collision_mono
#print axioms actual_run_collision_mono
#print axioms actual_used_insert_pair
#print axioms actual_fresh_new_step_current_unused
#print axioms actual_zero_collision_run_unused
#print axioms actual_initial_zero_collision_unused
end Reference.MD06OneCycle
