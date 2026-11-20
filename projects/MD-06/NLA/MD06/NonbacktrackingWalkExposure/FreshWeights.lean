module

public import NLA.MD06.NonbacktrackingWalkExposure.ReplySupport

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06ConditionalPartner
open Reference.MD06AdaptiveExposure Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_conditional_probability_false {n : ℕ} (C : Finset (Dart n × Dart n)) :
    ConditionalPairingProbability C (fun _ => False)=0 := by
  unfold ConditionalPairingProbability
  simp

theorem actual_conditional_probability_constant {n : ℕ} (C : Finset (Dart n × Dart n))
    (hp : 0<PatternCount C) (P : Prop) :
    ConditionalPairingProbability C (fun _ => P)=if P then 1 else 0 := by
  by_cases h : P
  · have hr : (PatternCount C : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hp
    unfold ConditionalPairingProbability
    have hc : Fintype.card {p : Pairing n // Matches C p ∧ P}=PatternCount C := by
      apply Fintype.card_congr
      exact {toFun:=fun p=>⟨p.val,p.property.1⟩
             invFun:=fun p=>⟨p.val,p.property,h⟩
             left_inv:=by intro p;rfl
             right_inv:=by intro p;rfl}
    rw [hc,div_self hr,if_pos h]
  · unfold ConditionalPairingProbability
    have he : IsEmpty {p : Pairing n // Matches C p ∧ P} := ⟨fun p=>h p.property.2⟩
    simp [h]

theorem actual_fresh_hit_weight (k : ℕ) (s : ExposureState (Size k)) (i : Fin 2)
    (hd : ∀ e∈s.exposed,e.1≠e.2)
    (hdis : ∀ e∈s.exposed,∀ f∈s.exposed,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (ha : s.current∉UsedDarts s.exposed) :
    (1/((FreePartners s.exposed s.current).card : ℝ))*
        ∑ b∈FreePartners s.exposed s.current,(if b.1∈s.visited then (1 : ℝ) else 0) =
      ConditionalPairingProbability s.exposed (fun p=>s.collisions<(ExposureStep p s i).collisions) := by
  rw [actual_step_collision_probability s i ha,
    actual_conditional_partner_uniform k s.exposed hd hdis s.current ha (VertexDarts s.visited)]
  have hs : (FreePartners s.exposed s.current).filter (fun b=>b.1∈s.visited)=
      VertexDarts s.visited ∩ FreePartners s.exposed s.current := by
    ext b
    simp [VertexDarts,and_comm]
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,one_div_mul_eq_div,mul_one]
  rw [hs]

#print axioms actual_conditional_probability_false
#print axioms actual_conditional_probability_constant
#print axioms actual_fresh_hit_weight
end Reference.MD06WalkExposure
