module

public import NLA.MD06.NonbacktrackingWalkExposure.CollisionTails
public import NLA.MD06.NonbacktrackingWalkExposure.MeanDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06ConditionalPartner
open Reference.MD06AdaptiveExposure Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

theorem actual_empty_conditional_probability {n : ℕ} (E : Pairing n → Prop) :
    ConditionalPairingProbability (∅ : Finset (Dart n × Dart n)) E=PairingProbability n E := by
  let e : {p : Pairing n // Matches ∅ p ∧ E p} ≃ {p : Pairing n // E p} :=
    {toFun:=fun p=>⟨p.val,p.property.2⟩
     invFun:=fun p=>⟨p.val,by simp [Matches],p.property⟩
     left_inv:=by intro p;rfl
     right_inv:=by intro p;rfl}
  let d : {p : Pairing n // Matches ∅ p} ≃ Pairing n :=
    {toFun:=Subtype.val
     invFun:=fun p=>⟨p,by simp [Matches]⟩
     left_inv:=by intro p;rfl
     right_inv:=by intro p;rfl}
  have hn:=Nat.card_congr e
  have hd:=Nat.card_congr d
  unfold ConditionalPairingProbability PairingProbability PatternCount
  simp only [Fintype.card_eq_nat_card]
  rw [hn,hd]

theorem actual_initial_collision_tails (k : ℕ) (a : Dart (Size k)) (w : List (Fin 2))
    (hpos : 0<3*Size k-2*w.length-1) :
    let β : ℝ:=((3*(w.length+1) : ℕ) : ℝ)/((3*Size k-2*w.length-1 : ℕ) : ℝ)
    PairingProbability (Size k) (fun p=>1≤(ExposureRun p (InitialState a) w).collisions) ≤
        (w.length : ℝ)*β ∧
      PairingProbability (Size k) (fun p=>2≤(ExposureRun p (InitialState a) w).collisions) ≤
        (w.length : ℝ)^2*β^2 := by
  have ht := actual_run_collision_tail_bounds k w.length (w.length+1) hpos w (InitialState a)
    (by simp [InitialState]) (by simp [InitialState])
    (by simp [InitialState]) (by simp [InitialState,Nat.add_comm])
  change ConditionalPairingProbability ∅ (fun p=>1≤(ExposureRun p (InitialState a) w).collisions) ≤ _ ∧
    ConditionalPairingProbability ∅ (fun p=>2≤(ExposureRun p (InitialState a) w).collisions) ≤ _ at ht
  simpa only [actual_empty_conditional_probability] using ht

theorem actual_initial_two_collision_bound (k : ℕ) (a : Dart (Size k)) (w : List (Fin 2))
    (hn : 2*w.length+1≤Size k) :
    PairingProbability (Size k) (fun p=>2≤(ExposureRun p (InitialState a) w).collisions) ≤
      9*(w.length : ℝ)^2*(w.length+1 : ℕ)^2/(Size k : ℝ)^2 := by
  have hn0 : 0<Size k := by unfold Size;omega
  have hpos : 0<3*Size k-2*w.length-1 := by omega
  have hden : Size k≤3*Size k-2*w.length-1 := by omega
  have hr0 : (0 : ℝ)<Size k := by exact_mod_cast hn0
  have hdenr : (Size k : ℝ)≤((3*Size k-2*w.length-1 : ℕ) : ℝ) := by exact_mod_cast hden
  have hb : ((3*(w.length+1) : ℕ) : ℝ)/((3*Size k-2*w.length-1 : ℕ) : ℝ) ≤
      ((3*(w.length+1) : ℕ) : ℝ)/(Size k : ℝ) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg _) hr0 hdenr
  have hb0 : (0 : ℝ)≤((3*(w.length+1) : ℕ) : ℝ)/((3*Size k-2*w.length-1 : ℕ) : ℝ) := by positivity
  have hs := sq_le_sq₀ hb0 (by positivity) |>.mpr hb
  have ht := (actual_initial_collision_tails k a w hpos).2
  calc
    _ ≤ (w.length : ℝ)^2*(((3*(w.length+1) : ℕ) : ℝ)/((3*Size k-2*w.length-1 : ℕ) : ℝ))^2 := ht
    _ ≤ (w.length : ℝ)^2*(((3*(w.length+1) : ℕ) : ℝ)/(Size k : ℝ))^2 :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,div_pow]
      ring

#print axioms actual_empty_conditional_probability
#print axioms actual_initial_collision_tails
#print axioms actual_initial_two_collision_bound
end Reference.MD06WalkExposure
