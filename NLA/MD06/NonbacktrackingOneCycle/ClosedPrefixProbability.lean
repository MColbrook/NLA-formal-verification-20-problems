module

public import NLA.MD06.NonbacktrackingOneCycle.TerminalMate
public import NLA.MD06.NonbacktrackingWalkExposure.CollisionConsequences

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
open Reference.MD06ConditionalPartner Reference.MD06AdaptiveExposure Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

theorem actual_port_choice_rev_right {n : ℕ} (a : Dart n) (i : Fin 2) :
    PortChoice (PortChoice a i) i.rev=a := by
  rcases a with ⟨v,j⟩
  fin_cases j <;> fin_cases i <;> norm_num [PortChoice,Fin.rev,Prod.ext_iff,Fin.ext_iff]

theorem actual_port_choice_fiber_rev {n : ℕ} (a b : Dart n) (i : Fin 2) :
    PortChoice b i=a ↔ b=PortChoice a i.rev := by
  constructor
  · intro h
    have hh:=congrArg (fun x : Dart n=>PortChoice x i.rev) h
    rw [actual_port_choice_rev_right] at hh
    exact hh
  · intro h
    rw [h]
    simpa only [Fin.rev_rev] using actual_port_choice_rev_right a i.rev

theorem actual_first_cycle_prefix_probability_bound (k : ℕ) (a : Dart (Size k))
    (u : List (Fin 2)) (i : Fin 2) (hpos : 0<3*Size k-2*u.length-1) :
    PairingProbability (Size k) (fun p=>
      (ExposureRun p (InitialState a) u).collisions=0 ∧
        (ExposureRun p (InitialState a) (u++[i])).current=a)≤
      1/((3*Size k-2*u.length-1 : ℕ) : ℝ) := by
  have ht:=actual_terminal_mate_zero_collision_bound k u.length hpos u (InitialState a)
    {PortChoice a i.rev} (by simp [InitialState]) (by simp [InitialState])
    (Finset.mem_singleton_self _) (by simp [InitialState,UsedDarts])
    (by simp [InitialState,UsedDarts]) (by simp [InitialState])
  have he : ConditionalPairingProbability (InitialState a).exposed (fun p=>
      (ExposureRun p (InitialState a) u).collisions=(InitialState a).collisions ∧
        p.val (ExposureRun p (InitialState a) u).current∈({PortChoice a i.rev} : Finset (Dart (Size k))))=
      ConditionalPairingProbability (InitialState a).exposed (fun p=>
        (ExposureRun p (InitialState a) u).collisions=0 ∧
          (ExposureRun p (InitialState a) (u++[i])).current=a) := by
    apply actual_conditional_event_congr
    intro p _
    simp only [Finset.mem_singleton,InitialState,actual_exposure_run_append,ExposureRun]
    change (_=0 ∧ p.val (ExposureRun p (InitialState a) u).current=PortChoice a i.rev) ↔
      (_=0 ∧ PortChoice (p.val (ExposureRun p (InitialState a) u).current) i=a)
    rw [actual_port_choice_fiber_rev]
  rw [he] at ht
  have hempty : (InitialState a).exposed=∅ := rfl
  rw [hempty,actual_empty_conditional_probability] at ht
  simpa only [Finset.card_singleton,Nat.cast_one] using ht

#print axioms actual_port_choice_rev_right
#print axioms actual_port_choice_fiber_rev
#print axioms actual_first_cycle_prefix_probability_bound
end Reference.MD06OneCycle
