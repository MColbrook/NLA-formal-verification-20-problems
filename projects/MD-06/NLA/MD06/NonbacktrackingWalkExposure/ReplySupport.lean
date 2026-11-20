module

public import NLA.MD06.NonbacktrackingWalkExposure.Support
public import NLA.MD06.NonbacktrackingWalkExposure.ProbabilityBasic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06ConditionalPartner
open Reference.MD06AdaptiveExposure Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

theorem actual_free_reply_represented (k : ℕ) (s : ExposureState (Size k)) (i : Fin 2)
    (hd : ∀ e∈s.exposed,e.1≠e.2)
    (hdis : ∀ e∈s.exposed,∀ f∈s.exposed,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (ha : s.current∉UsedDarts s.exposed) (b : Dart (Size k))
    (hb : b∈FreePartners s.exposed s.current) :
    ∃ p : Pairing (Size k),Matches s.exposed p ∧
      Matches (insert (s.current,b) s.exposed) p ∧ ExposureStep p s i=ReplyStep s i b := by
  obtain ⟨hd',hdis'⟩ := actual_insert_exposure_valid s.exposed hd hdis s.current b ha hb
  obtain ⟨p⟩ := actual_disjoint_pattern_nonempty k (insert (s.current,b) s.exposed) hd' hdis'
  refine ⟨p.val,?_,p.property,actual_insert_step_reply p.val s i b p.property⟩
  intro e he
  exact p.property e (Finset.mem_insert_of_mem he)

theorem actual_known_reply_represented (k : ℕ) (s : ExposureState (Size k)) (i : Fin 2)
    (hd : ∀ e∈s.exposed,e.1≠e.2)
    (hdis : ∀ e∈s.exposed,∀ f∈s.exposed,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (ha : s.current∈UsedDarts s.exposed) :
    ∃ p : Pairing (Size k),Matches s.exposed p ∧
      ExposureStep p s i=ReplyStep s i (ConstraintMate s.exposed s.current) := by
  obtain ⟨p⟩ := actual_disjoint_pattern_nonempty k s.exposed hd hdis
  exact ⟨p.val,p.property,actual_old_step_reply p.val s i p.property ha⟩

theorem actual_uniform_step_collision_bound (k : ℕ) (s : ExposureState (Size k)) (i : Fin 2)
    (hd : ∀ e∈s.exposed,e.1≠e.2)
    (hdis : ∀ e∈s.exposed,∀ f∈s.exposed,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (ha : s.current∉UsedDarts s.exposed) (T V : ℕ)
    (he : s.exposed.card≤T) (hv : s.visited.card≤V)
    (hp : 0<3*Size k-2*T-1) :
    ConditionalPairingProbability s.exposed (fun p => s.collisions<(ExposureStep p s i).collisions) ≤
      ((3*V : ℕ) : ℝ)/((3*Size k-2*T-1 : ℕ) : ℝ) := by
  have hn : 3*Size k-2*T-1≤3*Size k-2*s.exposed.card-1 := by omega
  have hr : ((3*Size k-2*T-1 : ℕ) : ℝ)≤((3*Size k-2*s.exposed.card-1 : ℕ) : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ)<((3*Size k-2*T-1 : ℕ) : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ ((3*s.visited.card : ℕ) : ℝ)/((3*Size k-2*s.exposed.card-1 : ℕ) : ℝ) :=
      actual_step_collision_probability_le k s i hd hdis ha
    _ ≤ ((3*V : ℕ) : ℝ)/((3*Size k-2*s.exposed.card-1 : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Nat.mul_le_mul_left 3 hv
    _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hpos hr

#print axioms actual_free_reply_represented
#print axioms actual_known_reply_represented
#print axioms actual_uniform_step_collision_bound
end Reference.MD06WalkExposure
