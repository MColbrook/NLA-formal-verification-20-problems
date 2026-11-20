module

public import NLA.MD06.NonbacktrackingWalkExposure.ReplyDefinitions
public import NLA.MD06.NonbacktrackingWalkExposure.StateBasic
public import NLA.MD06.AdaptiveExposure.Collision

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06ConditionalPartner
open Reference.MD06AdaptiveExposure Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_conditional_event_congr {n : ℕ} (C : Finset (Dart n × Dart n))
    (E F : Pairing n → Prop) (h : ∀ p, Matches C p → (E p ↔ F p)) :
    ConditionalPairingProbability C E=ConditionalPairingProbability C F := by
  let e : {p : Pairing n // Matches C p ∧ E p} ≃ {p : Pairing n // Matches C p ∧ F p} :=
    { toFun := fun p => ⟨p.val,p.property.1,(h p.val p.property.1).mp p.property.2⟩
      invFun := fun p => ⟨p.val,p.property.1,(h p.val p.property.1).mpr p.property.2⟩
      left_inv := by intro p;rfl
      right_inv := by intro p;rfl }
  exact congrArg (fun q : ℕ => (q : ℝ)/(PatternCount C : ℝ)) (Fintype.card_congr e)

theorem actual_step_reply {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2) :
    ExposureStep p s i=ReplyStep s i (p.val s.current) := rfl

theorem actual_insert_step_reply {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (b : Dart n) (hp : Matches (insert (s.current,b) s.exposed) p) :
    ExposureStep p s i=ReplyStep s i b := by
  have h := hp (s.current,b) (Finset.mem_insert_self _ _)
  change p.val s.current=b at h
  rw [actual_step_reply,h]

theorem actual_run_first_exposure_law (k : ℕ) (s : ExposureState (Size k)) (i : Fin 2)
    (w : List (Fin 2))
    (hd : ∀ e ∈ s.exposed,e.1≠e.2)
    (hdis : ∀ e ∈ s.exposed,∀ f ∈ s.exposed,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (ha : s.current ∉ UsedDarts s.exposed)
    (E : Pairing (Size k) → ExposureState (Size k) → Prop) :
    ConditionalPairingProbability s.exposed (fun p => E p (ExposureRun p s (i::w))) =
      (1/((FreePartners s.exposed s.current).card : ℝ)) *
        ∑ b ∈ FreePartners s.exposed s.current,
          ConditionalPairingProbability (insert (s.current,b) s.exposed)
            (fun p => E p (ExposureRun p (ReplyStep s i b) w)) := by
  rw [actual_conditional_exposure_law k s.exposed hd hdis s.current ha]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  apply actual_conditional_event_congr
  intro p hp
  rw [ExposureRun,actual_insert_step_reply p s i b hp]

theorem actual_step_collision_probability {n : ℕ} (s : ExposureState n) (i : Fin 2)
    (ha : s.current ∉ UsedDarts s.exposed) :
    ConditionalPairingProbability s.exposed (fun p => s.collisions < (ExposureStep p s i).collisions) =
      ConditionalPartnerProbability s.exposed s.current (VertexDarts s.visited) := by
  calc
    _ = ConditionalPairingProbability s.exposed
        (fun p => p.val s.current ∈ VertexDarts s.visited) := by
      apply actual_conditional_event_congr
      intro p _
      by_cases h : (p.val s.current).1 ∈ s.visited <;>
        simp [ExposureStep,ha,h,VertexDarts]
    _ = _ := by
      unfold ConditionalPairingProbability ConditionalPartnerProbability
      simp only [Fintype.card_eq_nat_card]


theorem actual_step_collision_probability_le (k : ℕ) (s : ExposureState (Size k)) (i : Fin 2)
    (hd : ∀ e ∈ s.exposed,e.1≠e.2)
    (hdis : ∀ e ∈ s.exposed,∀ f ∈ s.exposed,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (ha : s.current ∉ UsedDarts s.exposed) :
    ConditionalPairingProbability s.exposed (fun p => s.collisions < (ExposureStep p s i).collisions) ≤
      ((3*s.visited.card : ℕ) : ℝ)/((3*Size k-2*s.exposed.card-1 : ℕ) : ℝ) := by
  rw [actual_step_collision_probability s i ha]
  exact actual_conditional_hit_vertices_bound k s.exposed hd hdis s.current ha s.visited

#print axioms actual_conditional_event_congr

#print axioms actual_step_reply

#print axioms actual_insert_step_reply

#print axioms actual_run_first_exposure_law

#print axioms actual_step_collision_probability

#print axioms actual_step_collision_probability_le
end Reference.MD06WalkExposure
