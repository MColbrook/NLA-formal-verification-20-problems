module

public import NLA.MD06.NonbacktrackingWalkExposure.ConditionalStep
public import Mathlib.Data.Fintype.Card

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06AdaptiveExposure
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_conditional_probability_nonneg {n : ℕ} (C : Finset (Dart n × Dart n))
    (E : Pairing n → Prop) : 0≤ConditionalPairingProbability C E := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem actual_conditional_probability_mono {n : ℕ} (C : Finset (Dart n × Dart n))
    (E F : Pairing n → Prop) (h : ∀ p,Matches C p → E p → F p) :
    ConditionalPairingProbability C E≤ConditionalPairingProbability C F := by
  let f : {p : Pairing n // Matches C p ∧ E p} → {p : Pairing n // Matches C p ∧ F p} :=
    fun p => ⟨p.val,p.property.1,h p.val p.property.1 p.property.2⟩
  have hi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {p : Pairing n // Matches C p ∧ F p} => z.val) hab)
  have hc := Fintype.card_le_of_injective f hi
  unfold ConditionalPairingProbability
  exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)

theorem actual_conditional_probability_le_one {n : ℕ} (C : Finset (Dart n × Dart n))
    (E : Pairing n → Prop) : ConditionalPairingProbability C E≤1 := by
  let f : {p : Pairing n // Matches C p ∧ E p} → {p : Pairing n // Matches C p} :=
    fun p => ⟨p.val,p.property.1⟩
  have hi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun z : {p : Pairing n // Matches C p} => z.val) hab)
  have hc := Fintype.card_le_of_injective f hi
  unfold ConditionalPairingProbability
  by_cases hz : PatternCount C=0
  · simp [hz]
  · have hp : (0 : ℝ)<PatternCount C := by exact_mod_cast Nat.pos_of_ne_zero hz
    apply (div_le_one hp).mpr
    exact_mod_cast hc

theorem actual_conditional_probability_union_le {n : ℕ} (C : Finset (Dart n × Dart n))
    (E F : Pairing n → Prop) : ConditionalPairingProbability C (fun p => E p ∨ F p) ≤
      ConditionalPairingProbability C E+ConditionalPairingProbability C F := by
  let f : {p : Pairing n // Matches C p ∧ (E p ∨ F p)} →
      ({p : Pairing n // Matches C p ∧ E p} ⊕ {p : Pairing n // Matches C p ∧ F p}) :=
    fun p => if h : E p.val then Sum.inl ⟨p.val,p.property.1,h⟩
      else Sum.inr ⟨p.val,p.property.1,p.property.2.resolve_left h⟩
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have ha : (Sum.elim Subtype.val Subtype.val) (f a)=a.val := by simp [f];split_ifs <;> rfl
    have hb : (Sum.elim Subtype.val Subtype.val) (f b)=b.val := by simp [f];split_ifs <;> rfl
    rw [←ha,←hb,hab]
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_sum] at hc
  unfold ConditionalPairingProbability
  rw [←add_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [Fintype.card_eq_nat_card] at hc ⊢
  exact_mod_cast hc

theorem actual_finite_average_le {α : Type*} [DecidableEq α] (S : Finset α)
    (hp : 0<S.card) (f : α → ℝ) (L : ℝ) (h : ∀ a∈S,f a≤L) :
    (1/(S.card : ℝ))*∑ a∈S,f a≤L := by
  have hc : (0 : ℝ)<S.card := by exact_mod_cast hp
  have hs : (∑ a∈S,f a)≤(S.card : ℝ)*L := by
    calc
      _ ≤ ∑ _a∈S,L := Finset.sum_le_sum h
      _ = _ := by simp
  rw [one_div_mul_eq_div]
  exact (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hs)

#print axioms actual_conditional_probability_nonneg
#print axioms actual_conditional_probability_mono
#print axioms actual_conditional_probability_le_one
#print axioms actual_conditional_probability_union_le
#print axioms actual_finite_average_le
end Reference.MD06WalkExposure
