module

public import NLA.MD06.NonbacktrackingWalkExposure.PortChoices
public import NLA.MD06.AdaptiveExposure.Exposure
public import NLA.MD06.TwoExposure.Proofs

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06ConditionalPartner
open Reference.MD06AdaptiveExposure Reference.MD06TwoExposure
attribute [local instance] Classical.propDecidable

theorem actual_step_matches {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (hp : Matches s.exposed p) : Matches (ExposureStep p s i).exposed p := by
  change Matches (if s.current ∉ UsedDarts s.exposed then
    insert (s.current,p.val s.current) s.exposed else s.exposed) p
  by_cases h : s.current ∉ UsedDarts s.exposed
  · rw [if_pos h]
    intro e he
    rcases Finset.mem_insert.mp he with he | he
    · subst e;rfl
    · exact hp e he
  · rw [if_neg h]
    exact hp

theorem actual_step_valid {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (hd : ∀ e ∈ s.exposed,e.1≠e.2)
    (hdis : ∀ e ∈ s.exposed,∀ f ∈ s.exposed,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2})
    (hp : Matches s.exposed p) :
    (∀ e ∈ (ExposureStep p s i).exposed,e.1≠e.2) ∧
      (∀ e ∈ (ExposureStep p s i).exposed,∀ f ∈ (ExposureStep p s i).exposed,e≠f →
        Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) := by
  by_cases ha : s.current ∉ UsedDarts s.exposed
  · have hb : p.val s.current ∈ FreePartners s.exposed s.current := by
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact p.property.2 s.current h
      · exact (actual_matching_partner_outside s.exposed p hp s.current ha) h
    simpa [ExposureStep,ha] using actual_insert_exposure_valid s.exposed hd hdis
      s.current (p.val s.current) ha hb
  · simpa [ExposureStep,ha] using And.intro hd hdis

theorem actual_step_exposure_card {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2) :
    (ExposureStep p s i).exposed.card ≤ s.exposed.card+1 := by
  change (if s.current ∉ UsedDarts s.exposed then
    insert (s.current,p.val s.current) s.exposed else s.exposed).card ≤ _
  by_cases h : s.current ∉ UsedDarts s.exposed
  · rw [if_pos h]
    exact Finset.card_insert_le (s.current,p.val s.current) s.exposed
  · rw [if_neg h]
    omega

theorem actual_step_fresh_card {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2)
    (ha : s.current ∉ UsedDarts s.exposed) :
    (ExposureStep p s i).exposed.card=s.exposed.card+1 := by
  simpa [ExposureStep,ha] using actual_exposure_insert_card s.exposed s.current (p.val s.current) ha

theorem actual_step_visited_card {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2) :
    (ExposureStep p s i).visited.card ≤ s.visited.card+1 := by
  exact Finset.card_insert_le _ _

theorem actual_step_collision_card {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2) :
    (ExposureStep p s i).collisions ≤ s.collisions+1 := by
  change s.collisions+(if _ then 1 else 0) ≤ _
  split_ifs <;> omega

theorem actual_step_current_visited {n : ℕ} (p : Pairing n) (s : ExposureState n) (i : Fin 2) :
    (ExposureStep p s i).current.1 ∈ (ExposureStep p s i).visited := by
  exact Finset.mem_insert_self _ _

#print axioms actual_step_matches

#print axioms actual_step_valid

#print axioms actual_step_exposure_card

#print axioms actual_step_fresh_card

#print axioms actual_step_visited_card

#print axioms actual_step_collision_card

#print axioms actual_step_current_visited
end Reference.MD06WalkExposure
