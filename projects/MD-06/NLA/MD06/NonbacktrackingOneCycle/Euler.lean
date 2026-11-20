module

public import NLA.MD06.NonbacktrackingWalkExposure.Support

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_exposure_euler_step {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (hp : Matches s.exposed p) (hu : ∀ a∈UsedDarts s.exposed,a.1∈s.visited)
    (he : s.exposed.card+1=s.visited.card+s.collisions) :
    (ExposureStep p s i).exposed.card+1=
      (ExposureStep p s i).visited.card+(ExposureStep p s i).collisions := by
  by_cases ha : s.current∉UsedDarts s.exposed
  · have hc := actual_step_fresh_card p s i ha
    by_cases hv : (p.val s.current).1∈s.visited
    · have hvc : (ExposureStep p s i).visited.card=s.visited.card := by
        change (insert (p.val s.current).1 s.visited).card=s.visited.card
        rw [Finset.insert_eq_of_mem hv]
      have hcc : (ExposureStep p s i).collisions=s.collisions+1 := by simp [ExposureStep,ha,hv]
      rw [hc,hvc,hcc];omega
    · have hvc : (ExposureStep p s i).visited.card=s.visited.card+1 :=
        Finset.card_insert_of_notMem hv
      have hcc : (ExposureStep p s i).collisions=s.collisions := by simp [ExposureStep,ha,hv]
      rw [hc,hvc,hcc];omega
  · have ha' : s.current∈UsedDarts s.exposed := Classical.not_not.mp ha
    have hc : (ExposureStep p s i).exposed=s.exposed := by simp [ExposureStep,ha']
    have hv := actual_step_old_visited p s i hp hu ha'
    have hcc : (ExposureStep p s i).collisions=s.collisions := by simp [ExposureStep,ha']
    rw [hc,hv,hcc];exact he

theorem actual_exposure_euler_run {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2))
    (hp : Matches s.exposed p) (hc : s.current.1∈s.visited)
    (hu : ∀ a∈UsedDarts s.exposed,a.1∈s.visited)
    (he : s.exposed.card+1=s.visited.card+s.collisions) :
    (ExposureRun p s w).exposed.card+1=
      (ExposureRun p s w).visited.card+(ExposureRun p s w).collisions := by
  induction w generalizing s with
  | nil => exact he
  | cons i w ih =>
    exact ih (ExposureStep p s i) (actual_step_matches p s i hp)
      (actual_step_current_visited p s i) (actual_step_used_visited p s i hc hu)
      (actual_exposure_euler_step p s i hp hu he)

theorem actual_initial_exposure_euler {n : ℕ} (p : Pairing n) (a : Dart n) (w : List (Fin 2)) :
    (ExposureRun p (InitialState a) w).exposed.card+1=
      (ExposureRun p (InitialState a) w).visited.card+(ExposureRun p (InitialState a) w).collisions := by
  apply actual_exposure_euler_run
  · simp [InitialState,Matches]
  · exact Finset.mem_singleton_self _
  · simp [InitialState,UsedDarts]
  · simp [InitialState]

theorem actual_one_collision_edge_vertex_card {n : ℕ} (p : Pairing n) (a : Dart n) (w : List (Fin 2))
    (h : (ExposureRun p (InitialState a) w).collisions=1) :
    (ExposureRun p (InitialState a) w).exposed.card=(ExposureRun p (InitialState a) w).visited.card := by
  have he:=actual_initial_exposure_euler p a w
  rw [h] at he
  omega

#print axioms actual_exposure_euler_step
#print axioms actual_exposure_euler_run
#print axioms actual_initial_exposure_euler
#print axioms actual_one_collision_edge_vertex_card
end Reference.MD06OneCycle
