module

public import NLA.MD06.NonbacktrackingOneCycle.PortUpdates

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_unused_vertex_ports_empty {n : ℕ} (C : Finset (Dart n × Dart n)) (S : Finset (Fin n))
    (hu : ∀ a∈UsedDarts C,a.1∈S) (v : Fin n) (hv : v∉S) : UsedPorts C v=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hh:=Finset.mem_filter.mp ha
  exact hv (hh.2 ▸ hu a hh.1)

theorem actual_fresh_new_step_profile {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2) (a : Fin n)
    (ha : a∈s.visited) (hc : s.current.1∈s.visited)
    (hu : ∀ b∈UsedDarts s.exposed,b.1∈s.visited)
    (hf : s.current∉UsedDarts s.exposed) (hn : (p.val s.current).1∉s.visited)
    (hprofile : ∀ v∈s.visited,(UsedPorts s.exposed v).card+
      (if v=a then 1 else 0)+(if v=s.current.1 then 1 else 0)=2) :
    ∀ v∈(ExposureStep p s i).visited,(UsedPorts (ExposureStep p s i).exposed v).card+
      (if v=a then 1 else 0)+(if v=(ExposureStep p s i).current.1 then 1 else 0)=2 := by
  intro v hv
  change v∈insert (p.val s.current).1 s.visited at hv
  have hcard:=actual_fresh_new_step_ports p s i hc hu hf hn v
  have hcurr : (ExposureStep p s i).current.1=(p.val s.current).1 := actual_port_choice_fst _ _
  rw [hcurr]
  rcases Finset.mem_insert.mp hv with hv | hv
  · subst v
    have hp0 : (UsedPorts s.exposed (p.val s.current).1).card=0 := by
      rw [actual_unused_vertex_ports_empty s.exposed s.visited hu _ hn];rfl
    have hneq : (p.val s.current).1≠s.current.1 := by intro h;exact hn (h ▸ hc)
    have hna : (p.val s.current).1≠a := by intro h;exact hn (h ▸ ha)
    simp [hp0,hneq.symm] at hcard
    simp [hcard,hna]
  · have hnv : (p.val s.current).1≠v := by intro h;exact hn (h ▸ hv)
    have hpr:=hprofile v hv
    simpa [hcard,hnv,hnv.symm,eq_comm,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hpr

theorem actual_zero_collision_run_profile {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2))
    (a : Fin n) (ha : a∈s.visited) (hc : s.current.1∈s.visited)
    (hu : ∀ b∈UsedDarts s.exposed,b.1∈s.visited) (hf : s.current∉UsedDarts s.exposed)
    (hprofile : ∀ v∈s.visited,(UsedPorts s.exposed v).card+
      (if v=a then 1 else 0)+(if v=s.current.1 then 1 else 0)=2)
    (hz : (ExposureRun p s w).collisions=s.collisions) :
    ∀ v∈(ExposureRun p s w).visited,(UsedPorts (ExposureRun p s w).exposed v).card+
      (if v=a then 1 else 0)+(if v=(ExposureRun p s w).current.1 then 1 else 0)=2 := by
  induction w generalizing s with
  | nil => exact hprofile
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
    apply ih (ExposureStep p s i)
      (Finset.mem_insert_of_mem ha) (actual_step_current_visited p s i)
      (actual_step_used_visited p s i hc hu)
      (actual_fresh_new_step_current_unused p s i hc hu hf hn)
      (actual_fresh_new_step_profile p s i a ha hc hu hf hn hprofile)
    exact hz.trans hstep.symm

theorem actual_initial_zero_collision_profile {n : ℕ} (p : Pairing n) (a : Dart n) (w : List (Fin 2))
    (hz : (ExposureRun p (InitialState a) w).collisions=0) :
    ∀ v∈(ExposureRun p (InitialState a) w).visited,
      (UsedPorts (ExposureRun p (InitialState a) w).exposed v).card+
        (if v=a.1 then 1 else 0)+(if v=(ExposureRun p (InitialState a) w).current.1 then 1 else 0)=2 := by
  apply actual_zero_collision_run_profile p (InitialState a) w a.1
  · exact Finset.mem_singleton_self _
  · exact Finset.mem_singleton_self _
  · simp [InitialState,UsedDarts]
  · simp [InitialState,UsedDarts]
  · intro v hv
    have hh : v=a.1 := Finset.mem_singleton.mp hv
    subst v
    simp [InitialState,UsedPorts,UsedDarts]
  · exact hz

#print axioms actual_unused_vertex_ports_empty
#print axioms actual_fresh_new_step_profile
#print axioms actual_zero_collision_run_profile
#print axioms actual_initial_zero_collision_profile
end Reference.MD06OneCycle
