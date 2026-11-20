module

public import NLA.MD06.NonbacktrackingOneCycle.FirstReturn

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_two_port_support_subset_eq {n : ℕ} (C D : Finset (Dart n × Dart n)) (h : C⊆D)
    (b : Dart n) (hC : (UsedPorts C b.1).card=2) (hD : (UsedPorts D b.1).card≤2) :
    UsedPorts C b.1=UsedPorts D b.1 := by
  apply Finset.eq_of_subset_of_card_le (actual_used_ports_mono C D h b.1)
  omega

theorem actual_two_port_known_continuation {n : ℕ} (p : Pairing n)
    (C D : Finset (Dart n × Dart n)) (hCD : C⊆D) (hp : Matches C p)
    (hC : ∀ b∈UsedDarts C,(UsedPorts C b.1).card=2)
    (hD : ∀ b∈UsedDarts C,(UsedPorts D b.1).card≤2)
    (s : ExposureState n) (w : List (Fin 2)) (hs : s.exposed=C) (hc : s.current∈UsedDarts C)
    (hr : (ExposureRun p s w).exposed⊆D) (hend : (ExposureRun p s w).current∈UsedDarts D) :
    (ExposureRun p s w).current∈UsedDarts C ∧ (ExposureRun p s w).exposed=C := by
  induction w generalizing s with
  | nil => exact ⟨hc,hs⟩
  | cons i w ih =>
    have hb : p.val s.current∈UsedDarts C := actual_matching_partner_used C p hp s.current hc
    have hnD : (ExposureStep p s i).current∈UsedDarts D := by
      cases w with
      | nil => exact hend
      | cons j w =>
        exact actual_used_darts_mono _ _ hr (actual_first_current_used p (ExposureStep p s i) (j::w) (by simp))
    have hnP : (ExposureStep p s i).current∈UsedPorts D (p.val s.current).1 :=
      Finset.mem_filter.mpr ⟨hnD,actual_port_choice_fst _ _⟩
    have heq:=actual_two_port_support_subset_eq C D hCD (p.val s.current) (hC _ hb) (hD _ hb)
    have hnC : (ExposureStep p s i).current∈UsedDarts C :=
      (Finset.mem_filter.mp (heq ▸ hnP)).1
    have hs' : (ExposureStep p s i).exposed=C := by
      have hc' : s.current∈UsedDarts s.exposed := hs.symm ▸ hc
      change (if s.current∉UsedDarts s.exposed then insert (s.current,p.val s.current) s.exposed else s.exposed)=C
      rw [if_neg (Classical.not_not.mpr hc'),hs]
    exact ih (ExposureStep p s i) hs' hnC hr hend

theorem actual_one_collision_after_first_return_no_new_edges {n : ℕ} (p : Pairing n) (a : Dart n)
    (u z : List (Fin 2)) (i : Fin 2)
    (hz : (ExposureRun p (InitialState a) u).collisions=0)
    (hv : (p.val (ExposureRun p (InitialState a) u).current).1∈
      (ExposureRun p (InitialState a) u).visited)
    (hclosed : (ExposureRun p (InitialState a) (u++i::z)).current=a)
    (hc : (ExposureRun p (InitialState a) (u++i::z)).collisions=1) :
    (ExposureRun p (InitialState a) (u++[i])).exposed=
      (ExposureRun p (InitialState a) (u++i::z)).exposed := by
  let s:=ExposureRun p (InitialState a) (u++[i])
  let C:=s.exposed
  let D:=(ExposureRun p (InitialState a) (u++i::z)).exposed
  have hs : s.current=a := by
    simpa only [s,actual_exposure_run_append,ExposureRun] using actual_first_collision_returns_start p a u z i hz hv hclosed hc
  have hc1 : s.collisions=1 := by
    have hf:=actual_initial_zero_collision_unused p a u hz
    change (ExposureRun p (InitialState a) (u++[i])).collisions=1
    rw [actual_exposure_run_append,ExposureRun,ExposureRun]
    simp [ExposureStep,hf,hv,hz]
  have hCD : C⊆D := by
    simpa only [C,D,s,actual_exposure_run_append,ExposureRun] using actual_run_exposed_mono p s z
  have hp : Matches C p := actual_run_matches p (InitialState a) (u++[i]) (by simp [InitialState,Matches])
  have hC : ∀ b∈UsedDarts C,(UsedPorts C b.1).card=2 := by
    intro b hb
    exact actual_one_collision_used_ports_card p a (u++[i]) (by simp) hs hc1 _
      (actual_initial_run_used_visited p a (u++[i]) b hb)
  have hD : ∀ b∈UsedDarts C,(UsedPorts D b.1).card≤2 := by
    intro b hb
    have hh:=actual_initial_run_used_visited p a (u++i::z) b (actual_used_darts_mono C D hCD hb)
    exact le_of_eq (actual_one_collision_used_ports_card p a (u++i::z) (by simp) hclosed hc _ hh)
  have ha : s.current∈UsedDarts C := by
    rw [hs]
    exact actual_first_current_used p (InitialState a) (u++[i]) (by simp)
  have hr : (ExposureRun p s z).exposed=D := by
    simp only [s,D,actual_exposure_run_append,ExposureRun]
  have hend : (ExposureRun p s z).current∈UsedDarts D := by
    have hh : (ExposureRun p s z).current=a := by
      simpa only [s,actual_exposure_run_append,ExposureRun] using hclosed
    rw [hh]
    exact actual_first_current_used p (InitialState a) (u++i::z) (by simp)
  have result:=actual_two_port_known_continuation p C D hCD hp hC hD s z rfl ha (hr ▸ Finset.Subset.refl D) hend
  exact (hr.symm.trans result.2).symm

#print axioms actual_two_port_support_subset_eq
#print axioms actual_two_port_known_continuation
#print axioms actual_one_collision_after_first_return_no_new_edges
end Reference.MD06OneCycle
