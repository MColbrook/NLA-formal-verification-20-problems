module

public import NLA.MD06.NonbacktrackingWalkExposure.MultipleCollisionDefinitions
public import NLA.MD06.NonbacktrackingWalkExposure.WordExposure

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_pairing_mean_fiber_card (n : ℕ) {α β : Type*} [Fintype α] [Fintype β]
    (E : Pairing n → α → β → Prop) :
    PairingMean n (fun p=>((∑ a : α,Fintype.card {b : β // E p a b} : ℕ) : ℝ)) =
      ∑ a : α,∑ b : β,PairingProbability n (fun p=>E p a b) := by
  let e : (Σ p : Pairing n,Σ a : α,{b : β // E p a b}) ≃
      (Σ a : α,Σ b : β,{p : Pairing n // E p a b}) :=
    {toFun:=fun d=>⟨d.2.1,d.2.2.val,⟨d.1,d.2.2.property⟩⟩
     invFun:=fun d=>⟨d.2.2.val,d.1,⟨d.2.1,d.2.2.property⟩⟩
     left_inv:=by rintro ⟨p,a,⟨b,h⟩⟩;rfl
     right_inv:=by rintro ⟨a,b,⟨p,h⟩⟩;rfl}
  have hc := Fintype.card_congr e
  simp only [Fintype.card_sigma] at hc
  have hr : (∑ p : Pairing n,((∑ a : α,Fintype.card {b : β // E p a b} : ℕ) : ℝ)) =
      ∑ a : α,∑ b : β,(Fintype.card {p : Pairing n // E p a b} : ℝ) := by
    exact_mod_cast hc
  unfold PairingMean PairingProbability
  simp only [←Finset.sum_div]
  exact congrArg (fun z : ℝ=>z/(Fintype.card (Pairing n) : ℝ)) hr

theorem actual_multiple_collision_mean_identity (n t : ℕ) :
    MeanMultipleCollisionWords n t =
      ∑ a : Dart n,∑ w : Fin t→Fin 2,PairingProbability n
        (fun p=>2≤(ExposureRun p (InitialState a) (List.ofFn w)).collisions) := by
  simpa only [MeanMultipleCollisionWords,MultipleCollisionWords,Fintype.card_eq_nat_card] using
    actual_pairing_mean_fiber_card n
    (fun p a w=>2≤(ExposureRun p (InitialState a) (List.ofFn w)).collisions)

theorem actual_multiple_collision_mean_bound (k t : ℕ) (hn : 2*t+1≤Size k) :
    MeanMultipleCollisionWords (Size k) t ≤
      27*(t : ℝ)^2*(t+1 : ℕ)^2*2^t/(Size k : ℝ) := by
  rw [actual_multiple_collision_mean_identity]
  let C : ℝ:=9*(t : ℝ)^2*(t+1 : ℕ)^2/(Size k : ℝ)^2
  have hs : (∑ a : Dart (Size k),∑ w : Fin t→Fin 2,PairingProbability (Size k)
      (fun p=>2≤(ExposureRun p (InitialState a) (List.ofFn w)).collisions)) ≤
      ∑ _a : Dart (Size k),∑ _w : Fin t→Fin 2,C := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro w _
    exact actual_binary_word_two_collision_bound k t a w hn
  calc
    _ ≤ ∑ _a : Dart (Size k),∑ _w : Fin t→Fin 2,C := hs
    _ = ((Size k*3 : ℕ) : ℝ)*(2^t : ℕ)*C := by
      simp [nsmul_eq_mul,mul_assoc]
    _ = _ := by
      have hn0 : (Size k : ℝ)≠0 := by unfold Size;positivity
      dsimp only [C]
      simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Nat.cast_pow]
      field_simp [hn0]
      ring

#print axioms actual_pairing_mean_fiber_card
#print axioms actual_multiple_collision_mean_identity
#print axioms actual_multiple_collision_mean_bound
end Reference.MD06WalkExposure
