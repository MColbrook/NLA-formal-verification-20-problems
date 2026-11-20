module

public import NLA.MD06.DisjointTypedEnumeration.HeadDefinitions
public import NLA.MD06.DisjointTypedEnumeration.SubsetCardinality

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06JointSupportCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_head_false_card {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (HeadDatum S false) = 3*S.card := by
  let equiv : HeadDatum S false ≃ SupportedLoop S :=
    { toFun := by
        rintro ⟨d,hb,hs⟩
        cases d with
        | inl d => exact ⟨d,hs⟩
        | inr d => simp [IsDouble] at hb
      invFun := fun d => ⟨.inl d.val,rfl,d.property⟩
      left_inv := by
        rintro ⟨d,hb,hs⟩
        cases d with
        | inl d => rfl
        | inr d => simp [IsDouble] at hb
      right_inv := by rintro ⟨d,hs⟩;rfl }
  rw [Fintype.card_congr equiv,actual_supported_loop_card]

theorem actual_head_true_card {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (HeadDatum S true) = 18*S.card.choose 2 := by
  let equiv : HeadDatum S true ≃ SupportedDouble S :=
    { toFun := by
        rintro ⟨d,hb,hs⟩
        cases d with
        | inl d => simp [IsDouble] at hb
        | inr d => exact ⟨d,hs⟩
      invFun := fun d => ⟨.inr d.val,rfl,d.property⟩
      left_inv := by
        rintro ⟨d,hb,hs⟩
        cases d with
        | inl d => simp [IsDouble] at hb
        | inr d => rfl
      right_inv := by rintro ⟨d,hs⟩;rfl }
  rw [Fintype.card_congr equiv,actual_supported_double_card]

theorem actual_bad_vertex_count {n : ℕ} (d : BadDatum n) :
    (VertexSupport (BadPattern d)).card = if IsDouble d then 2 else 1 := by
  cases d with
  | inl d => simp [BadPattern,IsDouble,actual_loop_vertex_support]
  | inr d =>
    simp only [BadPattern,IsDouble,if_true,actual_double_vertex_support]
    simp [ne_of_lt d.1.property]

theorem actual_head_vertex_count {n : ℕ} (S : Finset (Fin n)) (b : Bool)
    (h : HeadDatum S b) :
    (VertexSupport (BadPattern h.val)).card = if b then 2 else 1 := by
  rw [actual_bad_vertex_count,h.property.1]

theorem actual_head_remaining_card {n : ℕ} (S : Finset (Fin n)) (b : Bool)
    (h : HeadDatum S b) :
    (S \ VertexSupport (BadPattern h.val)).card = S.card - (if b then 2 else 1) := by
  rw [Finset.card_sdiff_of_subset h.property.2,actual_head_vertex_count]

theorem actual_head_card {n : ℕ} (S : Finset (Fin n)) (b : Bool) :
    Fintype.card (HeadDatum S b) =
      3^(if b then 2 else 1) * S.card.descFactorial (if b then 2 else 1) := by
  cases b with
  | false => simp [actual_head_false_card]
  | true =>
    simp only [if_true,actual_head_true_card,Nat.descFactorial_eq_factorial_mul_choose]
    norm_num; ring

theorem actual_weight_zero (b : Fin 0 → Bool) : Weight b = 0 := by
  simp [Weight]

theorem actual_weight_succ {q : ℕ} (b : Fin (q+1) → Bool) :
    Weight b = (if b 0 then 2 else 1) + Weight (Fin.tail b) := by
  exact Fin.sum_univ_succ (fun i : Fin (q+1) => if b i then 2 else 1)

#print axioms actual_head_false_card
#print axioms actual_head_true_card
#print axioms actual_bad_vertex_count
#print axioms actual_head_vertex_count
#print axioms actual_head_remaining_card
#print axioms actual_head_card
#print axioms actual_weight_zero
#print axioms actual_weight_succ
end Reference.MD06DisjointTypedEnumeration
