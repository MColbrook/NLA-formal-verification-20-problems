module

public import NLA.MD06.NonbacktrackingOneCycle.MinimalPeriod

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

theorem actual_supported_word_unique_length {n : ℕ} (p : Pairing n) (C : Finset (Dart n × Dart n))
    (hp : Matches C p) (hC : ∀ b∈UsedDarts C,(UsedPorts C b.1).card=2)
    (s : ExposureState n) (u w : List (Fin 2)) (ha : s.current∈UsedDarts C)
    (hu : (ExposureRun p s u).exposed⊆C) (hue : (ExposureRun p s u).current∈UsedDarts C)
    (hw : (ExposureRun p s w).exposed⊆C) (hwe : (ExposureRun p s w).current∈UsedDarts C)
    (hlen : u.length=w.length) : u=w := by
  induction u generalizing s w with
  | nil => cases w with
    | nil => rfl
    | cons j w => simp at hlen
  | cons i u ih =>
    cases w with
    | nil => simp at hlen
    | cons j w =>
      have hni:=actual_next_current_used_of_run_support p s i u C hu hue
      have hnj:=actual_next_current_used_of_run_support p s j w C hw hwe
      have hi:=actual_supported_choice_eq p C hp hC s.current ha i hni
      have hj:=actual_supported_choice_eq p C hp hC s.current ha j hnj
      have hij : i=j := hi.symm.trans hj
      rw [←hij] at hw hwe hlen ⊢
      have ht : u=w := ih (ExposureStep p s i) w hni hu hue hw hwe (by simpa using hlen)
      rw [ht]

theorem actual_one_collision_support_unique_length {n : ℕ} (p : Pairing n) (a : Dart n)
    (u w : List (Fin 2)) (hu : (ExposureRun p (InitialState a) u).current=a)
    (huc : (ExposureRun p (InitialState a) u).collisions=1)
    (hw : (ExposureRun p (InitialState a) w).current=a)
    (_hwc : (ExposureRun p (InitialState a) w).collisions=1)
    (hs : (ExposureRun p (InitialState a) u).exposed=(ExposureRun p (InitialState a) w).exposed)
    (hlen : u.length=w.length) : u=w := by
  let C:=(ExposureRun p (InitialState a) u).exposed
  have hne : u≠[] := by intro h;subst u;change 0=1 at huc;omega
  have hp : Matches C p := actual_run_matches p (InitialState a) u (by simp [InitialState,Matches])
  have hC : ∀ b∈UsedDarts C,(UsedPorts C b.1).card=2 := by
    intro b hb
    exact actual_one_collision_used_ports_card p a u hne hu huc _ (actual_initial_run_used_visited p a u b hb)
  have ha : a∈UsedDarts C := actual_first_current_used p (InitialState a) u hne
  apply actual_supported_word_unique_length p C hp hC (InitialState a) u w ha
  · exact Finset.Subset.refl C
  · rw [hu];exact ha
  · rw [←hs]
  · simpa only [hw] using ha
  · exact hlen

#print axioms actual_supported_word_unique_length
#print axioms actual_one_collision_support_unique_length
end Reference.MD06OneCycle
