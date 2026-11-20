module

public import NLA.MD06.DisjointTypedEnumeration.HeadProperties

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06JointSupportCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_choice_tree_card (n q : ℕ) (S : Finset (Fin n)) (b : Fin q → Bool) :
    Fintype.card (ChoiceTree n q S b) =
      3^(Weight b) * S.card.descFactorial (Weight b) := by
  induction q generalizing S with
  | zero =>
    simp [ChoiceTree,Weight]
  | succ q ih =>
    let t : ℕ := if b 0 then 2 else 1
    let w : ℕ := Weight (Fin.tail b)
    have hweight : Weight b = t+w := actual_weight_succ b
    have hdesc : (S.card-t).descFactorial w * S.card.descFactorial t =
        S.card.descFactorial (t+w) := by
      have h := Nat.descFactorial_mul_descFactorial
        (n := S.card) (k := t) (m := t+w) (by omega : t ≤ t+w)
      simpa only [Nat.add_sub_cancel_left] using h
    change Fintype.card (Σ h : HeadDatum S (b 0),
      ChoiceTree n q (S \ VertexSupport (BadPattern h.val)) (Fin.tail b)) = _
    rw [Fintype.card_sigma]
    have hc (h : HeadDatum S (b 0)) :
        Fintype.card (ChoiceTree n q (S \ VertexSupport (BadPattern h.val)) (Fin.tail b)) =
          3^w*(S.card-t).descFactorial w := by
      rw [ih,actual_head_remaining_card]
    simp_rw [hc]
    rw [Finset.sum_const,Finset.card_univ,actual_head_card]
    simp only [nsmul_eq_mul,Nat.cast_id]
    rw [hweight]
    change (3^t*S.card.descFactorial t)*(3^w*(S.card-t).descFactorial w) =
      3^(t+w)*S.card.descFactorial (t+w)
    calc
      (3^t*S.card.descFactorial t)*(3^w*(S.card-t).descFactorial w) =
          3^(t+w)*((S.card-t).descFactorial w*S.card.descFactorial t) := by
        rw [pow_add]
        ring
      _ = 3^(t+w)*S.card.descFactorial (t+w) := by rw [hdesc]

#print axioms actual_choice_tree_card
end Reference.MD06DisjointTypedEnumeration
