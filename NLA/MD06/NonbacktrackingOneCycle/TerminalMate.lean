module

public import NLA.MD06.NonbacktrackingOneCycle.NoCollision
public import NLA.MD06.NonbacktrackingWalkExposure.CollisionTails

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
open Reference.MD06ConditionalPartner Reference.MD06AdaptiveExposure Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_terminal_mate_zero_collision_bound (k T : ℕ) (hpos : 0<3*Size k-2*T-1)
    (w : List (Fin 2)) (s : ExposureState (Size k)) (B : Finset (Dart (Size k)))
    (hd : ∀ e∈s.exposed,e.1≠e.2)
    (hdis : ∀ e∈s.exposed,∀ f∈s.exposed,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (hc : s.current.1∈s.visited) (hu : ∀ a∈UsedDarts s.exposed,a.1∈s.visited)
    (hf : s.current∉UsedDarts s.exposed) (he : s.exposed.card+w.length≤T) :
    ConditionalPairingProbability s.exposed (fun p=>
      (ExposureRun p s w).collisions=s.collisions ∧ p.val (ExposureRun p s w).current∈B)≤
        (B.card : ℝ)/((3*Size k-2*T-1 : ℕ) : ℝ) := by
  let A : ℝ:=(B.card : ℝ)/((3*Size k-2*T-1 : ℕ) : ℝ)
  have hA : 0≤A := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  change _≤A
  induction w generalizing s with
  | nil =>
    have hEq : ConditionalPairingProbability s.exposed (fun p=>
        (ExposureRun p s []).collisions=s.collisions ∧ p.val (ExposureRun p s []).current∈B)=
        ConditionalPartnerProbability s.exposed s.current B := by
      rw [actual_conditional_event_congr s.exposed _ (fun p=>p.val s.current∈B) (by intro p _;simp [ExposureRun])]
      unfold ConditionalPairingProbability ConditionalPartnerProbability
      simp only [Fintype.card_eq_nat_card]
    rw [hEq]
    have hb:=actual_conditional_partner_probability_le k s.exposed hd hdis s.current hf B
    apply le_trans hb
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast hpos)
    exact_mod_cast (show 3*Size k-2*T-1≤3*Size k-2*s.exposed.card-1 by simp only [List.length_nil,Nat.add_zero] at he;omega)
  | cons i w ih =>
    have hpoint (b : Dart (Size k)) (hb : b∈FreePartners s.exposed s.current) :
        ConditionalPairingProbability (insert (s.current,b) s.exposed) (fun p=>
          (ExposureRun p (ReplyStep s i b) w).collisions=s.collisions ∧
            p.val (ExposureRun p (ReplyStep s i b) w).current∈B)≤A := by
      by_cases hhit : b.1∈s.visited
      · have hcol : (ReplyStep s i b).collisions=s.collisions+1 := by simp [ReplyStep,hf,hhit]
        have hz : ConditionalPairingProbability (insert (s.current,b) s.exposed) (fun p=>
            (ExposureRun p (ReplyStep s i b) w).collisions=s.collisions ∧
              p.val (ExposureRun p (ReplyStep s i b) w).current∈B)=0 := by
          rw [actual_conditional_event_congr _ _ (fun _=>False) (by
            intro p _
            constructor
            · intro h
              have hm:=actual_run_collision_mono p (ReplyStep s i b) w
              rw [hcol,h.1] at hm
              omega
            · intro h;exact h.elim)]
          exact actual_conditional_probability_false _
        rw [hz];exact hA
      · obtain ⟨p,hp,hpi,hstep⟩:=actual_free_reply_represented k s i hd hdis hf b hb
        have hvalid:=actual_step_valid p s i hd hdis hp
        have hcur:=actual_step_current_visited p s i
        have hused:=actual_step_used_visited p s i hc hu
        have hmate : p.val s.current=b := hpi (s.current,b) (Finset.mem_insert_self _ _)
        have hnew : (p.val s.current).1∉s.visited := by rw [hmate];exact hhit
        have hfresh:=actual_fresh_new_step_current_unused p s i hc hu hf hnew
        have hcard:=actual_step_exposure_card p s i
        rw [hstep] at hvalid hcur hused hfresh hcard
        have hbudget : (ReplyStep s i b).exposed.card+w.length≤T := by simp only [List.length_cons] at he;omega
        have ht:=ih (ReplyStep s i b) hvalid.1 hvalid.2 hcur hused hfresh hbudget
        have hcol : (ReplyStep s i b).collisions=s.collisions := by simp [ReplyStep,hf,hhit]
        have hex : (ReplyStep s i b).exposed=insert (s.current,b) s.exposed := by simp [ReplyStep,hf]
        simpa only [hcol,hex] using ht
    rw [actual_run_first_exposure_law k s i w hd hdis hf
      (fun p z=>z.collisions=s.collisions ∧ p.val z.current∈B)]
    have hfree:=actual_free_partners_positive k s.exposed hd hdis s.current hf
    have havg:=actual_finite_average_indicator_bound (FreePartners s.exposed s.current) hfree
      (fun b=>ConditionalPairingProbability (insert (s.current,b) s.exposed) (fun p=>
        (ExposureRun p (ReplyStep s i b) w).collisions=s.collisions ∧
          p.val (ExposureRun p (ReplyStep s i b) w).current∈B))
      (fun _=>False) A 0 (by intro b hb;simpa using hpoint b hb)
    simpa using havg

#print axioms actual_terminal_mate_zero_collision_bound
end Reference.MD06OneCycle
