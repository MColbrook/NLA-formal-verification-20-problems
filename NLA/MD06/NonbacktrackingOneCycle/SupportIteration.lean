module

public import NLA.MD06.NonbacktrackingOneCycle.KnownContinuation
public import NLA.MD06.NonbacktrackingOneCycle.SupportNextDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_next_current_used_of_run_support {n : ℕ} (p : Pairing n) (s : ExposureState n)
    (i : Fin 2) (w : List (Fin 2)) (C : Finset (Dart n × Dart n))
    (hr : (ExposureRun p s (i::w)).exposed⊆C) (hend : (ExposureRun p s (i::w)).current∈UsedDarts C) :
    (ExposureStep p s i).current∈UsedDarts C := by
  cases w with
  | nil => exact hend
  | cons j w =>
    exact actual_used_darts_mono _ _ hr (actual_first_current_used p (ExposureStep p s i) (j::w) (by simp))

theorem actual_supported_choice_eq {n : ℕ} (p : Pairing n) (C : Finset (Dart n × Dart n))
    (hp : Matches C p) (hC : ∀ b∈UsedDarts C,(UsedPorts C b.1).card=2)
    (a : Dart n) (ha : a∈UsedDarts C) (i : Fin 2) (hi : PortChoice (p.val a) i∈UsedDarts C) :
    SupportedChoice p C a=i := by
  have hb:=actual_matching_partner_used C p hp a ha
  have he : ∃ j : Fin 2,PortChoice (p.val a) j∈UsedDarts C := ⟨i,hi⟩
  unfold SupportedChoice
  rw [dif_pos he]
  obtain ⟨j,hj,hu⟩:=actual_two_ports_unique_choice C (p.val a) hb (hC _ hb)
  exact (hu (Classical.choose he) (Classical.choose_spec he)).trans (hu i hi).symm

theorem actual_supported_run_iteration {n : ℕ} (p : Pairing n) (C : Finset (Dart n × Dart n))
    (hp : Matches C p) (hC : ∀ b∈UsedDarts C,(UsedPorts C b.1).card=2)
    (s : ExposureState n) (w : List (Fin 2)) (ha : s.current∈UsedDarts C)
    (hr : (ExposureRun p s w).exposed⊆C) (hend : (ExposureRun p s w).current∈UsedDarts C) :
    WalkEnd p s.current w=(SupportNext p C)^[w.length] s.current := by
  induction w generalizing s with
  | nil => rfl
  | cons i w ih =>
    have hn:=actual_next_current_used_of_run_support p s i w C hr hend
    have hchoice:=actual_supported_choice_eq p C hp hC s.current ha i hn
    have hs : SupportNext p C s.current=(ExposureStep p s i).current := by
      simp only [SupportNext,hchoice];rfl
    have hh:=ih (ExposureStep p s i) hn hr hend
    change WalkEnd p (ExposureStep p s i).current w=(SupportNext p C)^[w.length+1] s.current
    rw [Function.iterate_succ_apply,hs]
    exact hh

theorem actual_closed_prefix_iteration {n : ℕ} (p : Pairing n) (a : Dart n) (u z : List (Fin 2))
    (hw : u++z≠[]) (hclosed : (ExposureRun p (InitialState a) (u++z)).current=a)
    (hc : (ExposureRun p (InitialState a) (u++z)).collisions=1) :
    (ExposureRun p (InitialState a) u).current=
      (SupportNext p (ExposureRun p (InitialState a) (u++z)).exposed)^[u.length] a := by
  let C:=(ExposureRun p (InitialState a) (u++z)).exposed
  have hp : Matches C p := actual_run_matches p (InitialState a) (u++z) (by simp [InitialState,Matches])
  have hC : ∀ b∈UsedDarts C,(UsedPorts C b.1).card=2 := by
    intro b hb
    exact actual_one_collision_used_ports_card p a (u++z) hw hclosed hc _
      (actual_initial_run_used_visited p a (u++z) b hb)
  have ha : a∈UsedDarts C := actual_first_current_used p (InitialState a) (u++z) hw
  have hr : (ExposureRun p (InitialState a) u).exposed⊆C := by
    simpa only [C,actual_exposure_run_append] using actual_run_exposed_mono p (ExposureRun p (InitialState a) u) z
  have hend : (ExposureRun p (InitialState a) u).current∈UsedDarts C := by
    by_cases hz : z=[]
    · have he : (ExposureRun p (InitialState a) u).current=a := by simpa [hz] using hclosed
      rw [he];exact ha
    · simpa only [C,actual_exposure_run_append] using actual_first_current_used p (ExposureRun p (InitialState a) u) z hz
  rw [actual_run_end]
  exact actual_supported_run_iteration p C hp hC (InitialState a) u ha hr hend

#print axioms actual_next_current_used_of_run_support
#print axioms actual_supported_choice_eq
#print axioms actual_supported_run_iteration
#print axioms actual_closed_prefix_iteration
end Reference.MD06OneCycle
