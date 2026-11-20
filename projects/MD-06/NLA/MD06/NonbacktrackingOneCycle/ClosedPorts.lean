module

public import NLA.MD06.NonbacktrackingOneCycle.PrefixSupport

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_nonempty_list_last {α : Type*} (w : List α) (hw : w≠[]) :
    ∃ u : List α,∃ i : α,w=u++[i] := by
  induction w with
  | nil => exact (hw rfl).elim
  | cons i w ih =>
    by_cases h : w=[]
    · exact ⟨[],i,by simp [h]⟩
    · obtain ⟨u,j,hj⟩ := ih h
      exact ⟨i::u,j,by simp [hj]⟩

theorem actual_used_ports_two_of_mem {n : ℕ} (C : Finset (Dart n × Dart n)) (a b : Dart n)
    (ha : a∈UsedDarts C) (hb : b∈UsedDarts C) (hv : b.1=a.1) (hne : a≠b) :
    2≤(UsedPorts C a.1).card := by
  have hs : ({a,b} : Finset (Dart n))⊆UsedPorts C a.1 := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · subst x;simp [UsedPorts,ha]
    · subst x;simp [UsedPorts,hb,hv]
  simpa [hne] using Finset.card_le_card hs

theorem actual_closed_step_next_used {n : ℕ} (p : Pairing n) (s : ExposureState n)
    (u z : List (Fin 2)) (i : Fin 2)
    (hclosed : (ExposureRun p s (u++i::z)).current=s.current) :
    (ExposureStep p (ExposureRun p s u) i).current∈UsedDarts (ExposureRun p s (u++i::z)).exposed := by
  cases z with
  | nil =>
    have hu := actual_first_current_used p s (u++[i]) (by simp)
    have hc : (ExposureStep p (ExposureRun p s u) i).current=s.current := by
      simpa only [actual_exposure_run_append,ExposureRun] using hclosed
    rw [hc]
    exact hu
  | cons j z =>
    have hu := actual_first_current_used p (ExposureStep p (ExposureRun p s u) i) (j::z) (by simp)
    simpa only [actual_exposure_run_append,ExposureRun] using hu

theorem actual_closed_step_ports {n : ℕ} (p : Pairing n) (s : ExposureState n)
    (hp : Matches s.exposed p) (u z : List (Fin 2)) (i : Fin 2)
    (hclosed : (ExposureRun p s (u++i::z)).current=s.current) :
    2≤(UsedPorts (ExposureRun p s (u++i::z)).exposed (p.val (ExposureRun p s u).current).1).card := by
  have hb := (actual_step_darts_in_final p s hp u z i).2
  have hd := actual_closed_step_next_used p s u z i hclosed
  apply actual_used_ports_two_of_mem _ (p.val (ExposureRun p s u).current)
    (ExposureStep p (ExposureRun p s u) i).current hb hd
  · exact actual_port_choice_fst _ i
  · exact (actual_port_choice_ne _ i).symm

theorem actual_closed_visited_ports {n : ℕ} (p : Pairing n) (a : Dart n) (w : List (Fin 2))
    (hw : w≠[]) (hclosed : (ExposureRun p (InitialState a) w).current=a)
    (v : Fin n) (hv : v∈(ExposureRun p (InitialState a) w).visited) :
    2≤(UsedPorts (ExposureRun p (InitialState a) w).exposed v).card := by
  have hp : Matches (InitialState a).exposed p := by simp [InitialState,Matches]
  rcases actual_run_visited_witness p (InitialState a) w v hv with hv | ⟨u,z,i,hu,hv⟩
  · have hva : v=a.1 := Finset.mem_singleton.mp hv
    obtain ⟨u,i,hu⟩ := actual_nonempty_list_last w hw
    have hc : (ExposureRun p (InitialState a) (u++i::[])).current=(InitialState a).current := by
      simpa only [hu,InitialState] using hclosed
    have ht := actual_closed_step_ports p (InitialState a) hp u [] i hc
    have hx : (ExposureStep p (ExposureRun p (InitialState a) u) i).current=a := by
      simpa only [actual_exposure_run_append,ExposureRun,InitialState] using hc
    have hf : (p.val (ExposureRun p (InitialState a) u).current).1=a.1 := by
      have hf0:=congrArg (fun z : Dart n=>z.1) hx
      exact hf0
    rw [hf,←hu,←hva] at ht
    exact ht
  · have hc : (ExposureRun p (InitialState a) (u++i::z)).current=(InitialState a).current := by
      simpa only [hu,InitialState] using hclosed
    have ht := actual_closed_step_ports p (InitialState a) hp u z i hc
    rw [hv,←hu] at ht
    exact ht

#print axioms actual_nonempty_list_last
#print axioms actual_used_ports_two_of_mem
#print axioms actual_closed_step_next_used
#print axioms actual_closed_step_ports
#print axioms actual_closed_visited_ports
end Reference.MD06OneCycle
