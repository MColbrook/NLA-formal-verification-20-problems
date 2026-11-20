module

public import NLA.MD06.NonbacktrackingOneCycle.PathProfile

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_run_visited_mono {n : ℕ} (p : Pairing n) (s : ExposureState n) (w : List (Fin 2)) :
    s.visited⊆(ExposureRun p s w).visited := by
  induction w generalizing s with
  | nil => exact Finset.Subset.refl _
  | cons i w ih => exact Finset.Subset.trans (Finset.subset_insert _ _) (ih (ExposureStep p s i))

theorem actual_used_ports_mono {n : ℕ} (C D : Finset (Dart n × Dart n)) (h : C⊆D) (v : Fin n) :
    UsedPorts C v⊆UsedPorts D v := by
  intro a ha
  have hh:=Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨actual_used_darts_mono C D h hh.1,hh.2⟩

theorem actual_used_ports_insert_same {n : ℕ} (C : Finset (Dart n × Dart n)) (a b : Dart n)
    (ha : a∉UsedDarts C) (hb : b∉UsedDarts C) (hab : a≠b) (hv : b.1=a.1) :
    (UsedPorts (insert (a,b) C) a.1).card=(UsedPorts C a.1).card+2 := by
  have he : UsedPorts (insert (a,b) C) a.1=insert a (insert b (UsedPorts C a.1)) := by
    ext d
    simp [UsedPorts,actual_used_insert_pair]
    aesop
  have hnotb : b∉UsedPorts C a.1 := by intro h;exact hb (Finset.mem_filter.mp h).1
  have hnota : a∉insert b (UsedPorts C a.1) := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hab h
    · exact ha (Finset.mem_filter.mp h).1
  rw [he,Finset.card_insert_of_notMem hnota,Finset.card_insert_of_notMem hnotb]

theorem actual_first_collision_hits_start {n : ℕ} (p : Pairing n) (a : Dart n)
    (u z : List (Fin 2)) (i : Fin 2)
    (hz : (ExposureRun p (InitialState a) u).collisions=0)
    (hv : (p.val (ExposureRun p (InitialState a) u).current).1∈
      (ExposureRun p (InitialState a) u).visited)
    (hclosed : (ExposureRun p (InitialState a) (u++i::z)).current=a)
    (hc : (ExposureRun p (InitialState a) (u++i::z)).collisions=1) :
    (p.val (ExposureRun p (InitialState a) u).current).1=a.1 := by
  let s:=ExposureRun p (InitialState a) u
  have hf : s.current∉UsedDarts s.exposed := actual_initial_zero_collision_unused p a u hz
  have hp : Matches s.exposed p := actual_run_matches p (InitialState a) u (by simp [InitialState,Matches])
  have hb := actual_matching_partner_outside s.exposed p hp s.current hf
  have hm : (ExposureStep p s i).exposed⊆(ExposureRun p (InitialState a) (u++i::z)).exposed := by
    simpa only [actual_exposure_run_append,ExposureRun] using actual_run_exposed_mono p (ExposureStep p s i) z
  have hfv : (p.val s.current).1∈(ExposureRun p (InitialState a) (u++i::z)).visited := by
    rw [actual_exposure_run_append,ExposureRun]
    exact actual_run_visited_mono p (ExposureStep p s i) z (Finset.mem_insert_self _ _)
  have hbound : (UsedPorts (ExposureStep p s i).exposed (p.val s.current).1).card≤2 := by
    calc
      _ ≤ (UsedPorts (ExposureRun p (InitialState a) (u++i::z)).exposed (p.val s.current).1).card :=
        Finset.card_le_card (actual_used_ports_mono _ _ hm _)
      _ = 2 := actual_one_collision_used_ports_card p a (u++i::z) (by simp) hclosed hc _ hfv
  have hprofile := actual_initial_zero_collision_profile p a u hz (p.val s.current).1 hv
  change (UsedPorts s.exposed (p.val s.current).1).card+
    (if (p.val s.current).1=a.1 then 1 else 0)+(if (p.val s.current).1=s.current.1 then 1 else 0)=2 at hprofile
  by_contra hstart
  change (p.val s.current).1≠a.1 at hstart
  by_cases heq : (p.val s.current).1=s.current.1
  · have hinc : (UsedPorts (ExposureStep p s i).exposed (p.val s.current).1).card=
        (UsedPorts s.exposed (p.val s.current).1).card+2 := by
      change (UsedPorts (if s.current∉UsedDarts s.exposed then insert (s.current,p.val s.current) s.exposed else s.exposed) _).card=_
      rw [if_pos hf,heq]
      exact actual_used_ports_insert_same s.exposed s.current (p.val s.current) hf hb (p.property.2 s.current).symm heq
    simp only [if_neg hstart,if_pos heq] at hprofile
    omega
  · have hinc : (UsedPorts (ExposureStep p s i).exposed (p.val s.current).1).card=
        (UsedPorts s.exposed (p.val s.current).1).card+1 := by
      change (UsedPorts (if s.current∉UsedDarts s.exposed then insert (s.current,p.val s.current) s.exposed else s.exposed) _).card=_
      rw [if_pos hf]
      exact actual_used_ports_insert_at_second s.exposed s.current (p.val s.current) hb (Ne.symm heq)
    simp only [if_neg hstart,if_neg heq] at hprofile
    omega

theorem actual_first_collision_returns_start {n : ℕ} (p : Pairing n) (a : Dart n)
    (u z : List (Fin 2)) (i : Fin 2)
    (hz : (ExposureRun p (InitialState a) u).collisions=0)
    (hv : (p.val (ExposureRun p (InitialState a) u).current).1∈
      (ExposureRun p (InitialState a) u).visited)
    (hclosed : (ExposureRun p (InitialState a) (u++i::z)).current=a)
    (hc : (ExposureRun p (InitialState a) (u++i::z)).collisions=1) :
    (ExposureStep p (ExposureRun p (InitialState a) u) i).current=a := by
  let s:=ExposureRun p (InitialState a) u
  let C:=(ExposureRun p (InitialState a) (u++i::z)).exposed
  have hstart : (p.val s.current).1=a.1 := actual_first_collision_hits_start p a u z i hz hv hclosed hc
  have hp : Matches s.exposed p := actual_run_matches p (InitialState a) u (by simp [InitialState,Matches])
  have hf := actual_initial_zero_collision_unused p a u hz
  have hba : p.val s.current≠a := by
    by_cases hu : u=[]
    · subst u;exact p.property.2 a
    · intro h
      have hused:=actual_first_current_used p (InitialState a) u hu
      exact actual_matching_partner_outside s.exposed p hp s.current hf (h ▸ hused)
  have hd := actual_closed_step_next_used p (InitialState a) u z i hclosed
  have ha : a∈UsedDarts C := actual_first_current_used p (InitialState a) (u++i::z) (by simp)
  have hb : p.val s.current∈UsedDarts C := (actual_step_darts_in_final p (InitialState a) (by simp [InitialState,Matches]) u z i).2
  have hvc : (p.val s.current).1∈(ExposureRun p (InitialState a) (u++i::z)).visited := by
    rw [actual_exposure_run_append,ExposureRun]
    exact actual_run_visited_mono p (ExposureStep p s i) z (Finset.mem_insert_self _ _)
  have ht:=actual_one_collision_used_ports_card p a (u++i::z) (by simp) hclosed hc _ hvc
  obtain ⟨j,hj⟩:=actual_port_choices_exhaustive (p.val s.current) a hstart hba
  obtain ⟨l,hl,hu⟩:=actual_two_ports_unique_choice C (p.val s.current) hb ht
  have hi : i=l := hu i hd
  have hjmem : PortChoice (p.val s.current) j∈UsedDarts C := by rw [hj];exact ha
  have hjl : j=l := hu j hjmem
  change PortChoice (p.val s.current) i=a
  rw [hi,←hjl,hj]

#print axioms actual_run_visited_mono
#print axioms actual_used_ports_mono
#print axioms actual_used_ports_insert_same
#print axioms actual_first_collision_hits_start
#print axioms actual_first_collision_returns_start
end Reference.MD06OneCycle
