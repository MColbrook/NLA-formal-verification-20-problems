module

public import NLA.MD06.NonbacktrackingWalkExposure.KnownMateDefinitions
public import NLA.MD06.NonbacktrackingWalkExposure.ConditionalStep

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06AdaptiveExposure
attribute [local instance] Classical.propDecidable

theorem actual_used_constraint_witness {n : ℕ} (C : Finset (Dart n × Dart n)) (a : Dart n) :
    a∈UsedDarts C ↔ ∃ e : Dart n × Dart n,e∈C ∧ (a=e.1 ∨ a=e.2) := by
  constructor
  · intro ha
    obtain ⟨e,he,ha⟩ := Finset.mem_biUnion.mp ha
    exact ⟨e,he,by simpa only [Finset.mem_insert,Finset.mem_singleton] using ha⟩
  · rintro ⟨e,he,ha⟩
    exact Finset.mem_biUnion.mpr ⟨e,he,by simpa only [Finset.mem_insert,Finset.mem_singleton] using ha⟩

theorem actual_constraint_mate {n : ℕ} (C : Finset (Dart n × Dart n)) (p : Pairing n)
    (hp : Matches C p) (a : Dart n) (ha : a∈UsedDarts C) : p.val a=ConstraintMate C a := by
  have hw := (actual_used_constraint_witness C a).mp ha
  rw [ConstraintMate,dif_pos hw]
  let e := Classical.choose hw
  have he : e∈C ∧ (a=e.1 ∨ a=e.2) := Classical.choose_spec hw
  change p.val a=if a=e.1 then e.2 else e.1
  by_cases h : a=e.1
  · rw [if_pos h,h];exact hp e he.1
  · rw [if_neg h,he.2.resolve_left h]
    rw [← hp e he.1]
    exact p.property.1 e.1

theorem actual_matching_partner_used {n : ℕ} (C : Finset (Dart n × Dart n)) (p : Pairing n)
    (hp : Matches C p) (a : Dart n) (ha : a∈UsedDarts C) : p.val a∈UsedDarts C := by
  obtain ⟨e,he,ha⟩ := (actual_used_constraint_witness C a).mp ha
  have h := actual_pattern_endpoints_used C e he
  rcases ha with ha | ha
  · rw [ha,hp e he];exact h.2
  · rw [ha,← hp e he,p.property.1 e.1];exact h.1

theorem actual_old_step_reply {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (hp : Matches s.exposed p) (ha : s.current∈UsedDarts s.exposed) :
    ExposureStep p s i=ReplyStep s i (ConstraintMate s.exposed s.current) := by
  rw [actual_step_reply,actual_constraint_mate s.exposed p hp s.current ha]

theorem actual_run_first_known_law {n : ℕ} (s : ExposureState n) (i : Fin 2) (w : List (Fin 2))
    (ha : s.current∈UsedDarts s.exposed) (E : Pairing n → ExposureState n → Prop) :
    ConditionalPairingProbability s.exposed (fun p => E p (ExposureRun p s (i::w))) =
      ConditionalPairingProbability s.exposed
        (fun p => E p (ExposureRun p (ReplyStep s i (ConstraintMate s.exposed s.current)) w)) := by
  apply actual_conditional_event_congr
  intro p hp
  rw [ExposureRun,actual_old_step_reply p s i hp ha]

#print axioms actual_used_constraint_witness

#print axioms actual_constraint_mate

#print axioms actual_matching_partner_used

#print axioms actual_old_step_reply

#print axioms actual_run_first_known_law
end Reference.MD06WalkExposure
