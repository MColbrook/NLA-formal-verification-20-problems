module

public import NLA.MD06.NonbacktrackingWalkExposure.FreshWeights
public import NLA.MD06.NonbacktrackingWalkExposure.AverageIndicators

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06ConditionalPartner
open Reference.MD06AdaptiveExposure Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_run_collision_tail_bounds (k T V : ℕ) (hpos : 0<3*Size k-2*T-1)
    (w : List (Fin 2)) (s : ExposureState (Size k))
    (hd : ∀ e∈s.exposed,e.1≠e.2)
    (hdis : ∀ e∈s.exposed,∀ f∈s.exposed,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (he : s.exposed.card+w.length≤T) (hv : s.visited.card+w.length≤V) :
    let β : ℝ:=((3*V : ℕ) : ℝ)/((3*Size k-2*T-1 : ℕ) : ℝ)
    ConditionalPairingProbability s.exposed (fun p=>s.collisions+1≤(ExposureRun p s w).collisions) ≤
        (w.length : ℝ)*β ∧
      ConditionalPairingProbability s.exposed (fun p=>s.collisions+2≤(ExposureRun p s w).collisions) ≤
        (w.length : ℝ)^2*β^2 := by
  let β : ℝ:=((3*V : ℕ) : ℝ)/((3*Size k-2*T-1 : ℕ) : ℝ)
  have hβ : 0≤β := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  change _≤(w.length : ℝ)*β ∧ _≤(w.length : ℝ)^2*β^2
  induction w generalizing s with
  | nil =>
    have hz (r : ℕ) (hr : 0<r) : ConditionalPairingProbability s.exposed
        (fun p=>s.collisions+r≤(ExposureRun p s []).collisions)=0 := by
      rw [actual_conditional_event_congr s.exposed _ (fun _=>False) (by
        intro p _
        change (s.collisions+r≤s.collisions)↔False
        constructor
        · intro h;omega
        · intro h;exact h.elim)]
      exact actual_conditional_probability_false s.exposed
    constructor
    · rw [hz 1 (by omega)];simp
    · rw [hz 2 (by omega)];simp
  | cons i w ih =>
    have hL : 0≤(w.length : ℝ)*β := mul_nonneg (Nat.cast_nonneg _) hβ
    have hQ : 0≤(w.length : ℝ)^2*β^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    by_cases ha : s.current∉UsedDarts s.exposed
    · let H : Dart (Size k) → Prop:=fun b=>b.1∈s.visited
      have hmEq : (1/((FreePartners s.exposed s.current).card : ℝ))*
          ∑ b∈FreePartners s.exposed s.current,(if H b then (1 : ℝ) else 0) =
          (1/((FreePartners s.exposed s.current).card : ℝ))*
            ∑ b∈FreePartners s.exposed s.current,(if b.1∈s.visited then (1 : ℝ) else 0) := by
        rfl
      have htail (b : Dart (Size k)) (hb : b∈FreePartners s.exposed s.current) :
          ConditionalPairingProbability (insert (s.current,b) s.exposed)
              (fun p=>(ReplyStep s i b).collisions+1≤(ExposureRun p (ReplyStep s i b) w).collisions) ≤
              (w.length : ℝ)*β ∧
            ConditionalPairingProbability (insert (s.current,b) s.exposed)
              (fun p=>(ReplyStep s i b).collisions+2≤(ExposureRun p (ReplyStep s i b) w).collisions) ≤
              (w.length : ℝ)^2*β^2 := by
        obtain ⟨p,hp,_hpi,hstep⟩ := actual_free_reply_represented k s i hd hdis ha b hb
        have hvalid := actual_step_valid p s i hd hdis hp
        have hec := actual_step_exposure_card p s i
        have hvc := actual_step_visited_card p s i
        rw [hstep] at hvalid hec hvc
        have he' : (ReplyStep s i b).exposed.card+w.length≤T := by simp only [List.length_cons] at he;omega
        have hv' : (ReplyStep s i b).visited.card+w.length≤V := by simp only [List.length_cons] at hv;omega
        have ht := ih (ReplyStep s i b) hvalid.1 hvalid.2 he' hv'
        have hex : (ReplyStep s i b).exposed=insert (s.current,b) s.exposed := by simp [ReplyStep,ha]
        simpa only [hex] using ht
      have hfree : 0<(FreePartners s.exposed s.current).card :=
        actual_free_partners_positive k s.exposed hd hdis s.current ha
      have hmass : (1/((FreePartners s.exposed s.current).card : ℝ))*
          ∑ b∈FreePartners s.exposed s.current,(if H b then (1 : ℝ) else 0) ≤β := by
        rw [hmEq,actual_fresh_hit_weight k s i hd hdis ha]
        exact actual_uniform_step_collision_bound k s i hd hdis ha T V (by omega) (by omega) hpos
      constructor
      · have hpoint (b : Dart (Size k)) (hb : b∈FreePartners s.exposed s.current) :
            ConditionalPairingProbability (insert (s.current,b) s.exposed)
              (fun p=>s.collisions+1≤(ExposureRun p (ReplyStep s i b) w).collisions) ≤
                (w.length : ℝ)*β+(if H b then (1 : ℝ) else 0) := by
          by_cases hhit : b.1∈s.visited
          · have hp1 := actual_conditional_probability_le_one (insert (s.current,b) s.exposed)
                (fun p=>s.collisions+1≤(ExposureRun p (ReplyStep s i b) w).collisions)
            rw [if_pos (show H b from hhit)];linarith
          · have hcol : (ReplyStep s i b).collisions=s.collisions := by simp [ReplyStep,ha,hhit]
            have ht := (htail b hb).1
            rw [hcol] at ht
            simpa only [if_neg (show ¬H b from hhit),add_zero] using ht
        rw [actual_run_first_exposure_law k s i w hd hdis ha
          (fun _ z=>s.collisions+1≤z.collisions)]
        have havg := actual_finite_average_indicator_bound (FreePartners s.exposed s.current) hfree
          (fun b=>ConditionalPairingProbability (insert (s.current,b) s.exposed)
            (fun p=>s.collisions+1≤(ExposureRun p (ReplyStep s i b) w).collisions))
          H ((w.length : ℝ)*β) 1 hpoint
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        nlinarith
      · have hpoint (b : Dart (Size k)) (hb : b∈FreePartners s.exposed s.current) :
            ConditionalPairingProbability (insert (s.current,b) s.exposed)
              (fun p=>s.collisions+2≤(ExposureRun p (ReplyStep s i b) w).collisions) ≤
                (w.length : ℝ)^2*β^2+(if H b then (w.length : ℝ)*β else 0) := by
          by_cases hhit : b.1∈s.visited
          · have hcol : (ReplyStep s i b).collisions=s.collisions+1 := by simp [ReplyStep,ha,hhit]
            have ht := (htail b hb).1
            rw [hcol] at ht
            have hp1 : ConditionalPairingProbability (insert (s.current,b) s.exposed)
                (fun p=>s.collisions+2≤(ExposureRun p (ReplyStep s i b) w).collisions) ≤(w.length : ℝ)*β := by
              apply le_trans (actual_conditional_probability_mono _ _ _ (by intro p _ h;omega)) ht
            rw [if_pos (show H b from hhit)];linarith
          · have hcol : (ReplyStep s i b).collisions=s.collisions := by simp [ReplyStep,ha,hhit]
            have ht := (htail b hb).2
            rw [hcol] at ht
            simpa only [if_neg (show ¬H b from hhit),add_zero] using ht
        rw [actual_run_first_exposure_law k s i w hd hdis ha
          (fun _ z=>s.collisions+2≤z.collisions)]
        have havg := actual_finite_average_indicator_bound (FreePartners s.exposed s.current) hfree
          (fun b=>ConditionalPairingProbability (insert (s.current,b) s.exposed)
            (fun p=>s.collisions+2≤(ExposureRun p (ReplyStep s i b) w).collisions))
          H ((w.length : ℝ)^2*β^2) ((w.length : ℝ)*β) hpoint
        have hmul := mul_le_mul_of_nonneg_right hmass hL
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        nlinarith [sq_nonneg β]
    · have ha' : s.current∈UsedDarts s.exposed := Classical.not_not.mp ha
      obtain ⟨p,hp,hstep⟩ := actual_known_reply_represented k s i hd hdis ha'
      let z:=ReplyStep s i (ConstraintMate s.exposed s.current)
      have hvalid := actual_step_valid p s i hd hdis hp
      have hec := actual_step_exposure_card p s i
      have hvc := actual_step_visited_card p s i
      rw [hstep] at hvalid hec hvc
      have he' : z.exposed.card+w.length≤T := by
        change (ReplyStep s i (ConstraintMate s.exposed s.current)).exposed.card+w.length≤T
        simp only [List.length_cons] at he;omega
      have hv' : z.visited.card+w.length≤V := by
        change (ReplyStep s i (ConstraintMate s.exposed s.current)).visited.card+w.length≤V
        simp only [List.length_cons] at hv;omega
      have ht := ih z hvalid.1 hvalid.2 he' hv'
      have hex : z.exposed=s.exposed := by simp [z,ReplyStep,ha']
      have hcol : z.collisions=s.collisions := by simp [z,ReplyStep,ha']
      rw [hex,hcol] at ht
      constructor
      · rw [actual_run_first_known_law s i w ha' (fun _ z=>s.collisions+1≤z.collisions)]
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        exact le_trans ht.1 (by nlinarith)
      · rw [actual_run_first_known_law s i w ha' (fun _ z=>s.collisions+2≤z.collisions)]
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
        exact le_trans ht.2 (by nlinarith [sq_nonneg β])

#print axioms actual_run_collision_tail_bounds
end Reference.MD06WalkExposure
