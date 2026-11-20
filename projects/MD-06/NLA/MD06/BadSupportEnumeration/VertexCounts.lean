module

public import NLA.MD06.BadSupportEnumeration.JointCounts
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadSupportEnumeration
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
open Reference.MD06BadJointMoments Reference.MD06JointSupportCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_vertex_sets_card (n v : ℕ) :
    Fintype.card {S : Finset (Fin n) // S.card = v} = n.choose v := by
  let e : {S : Finset (Fin n) // S.card = v} ≃
      {S : Finset (Fin n) // S ∈ (Finset.univ : Finset (Fin n)).powersetCard v} :=
    { toFun := fun S => ⟨S.val,by simp [Finset.mem_powersetCard,S.property]⟩
      invFun := fun S => ⟨S.val,(Finset.mem_powersetCard.mp S.property).2⟩
      left_inv := by intro S;rfl
      right_inv := by intro S;rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_coe] at h
  simpa only [Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin] using h

theorem actual_joint_given_vertex_count_card_le (n q v : ℕ) :
    Fintype.card {f : JointDatum n q // (VertexSupport (JointPattern f)).card = v} ≤
      n.choose v * (3*v+18*v^2)^q := by
  let encode :
      {f : JointDatum n q // (VertexSupport (JointPattern f)).card = v} →
      (Σ S : {S : Finset (Fin n) // S.card = v}, SupportedJointDatum n q S.val) :=
    fun f => ⟨⟨VertexSupport (JointPattern f.val),f.property⟩,
      ⟨f.val,Finset.Subset.refl _⟩⟩
  have hi : Function.Injective encode := by
    intro f g h
    apply Subtype.ext
    exact congrArg (fun z => z.2.val) h
  have hc := Fintype.card_le_of_injective encode hi
  rw [Fintype.card_sigma] at hc
  have hs : (∑ S : {S : Finset (Fin n) // S.card = v},
      Fintype.card (SupportedJointDatum n q S.val)) ≤
        ∑ S : {S : Finset (Fin n) // S.card = v}, (3*v+18*v^2)^q := by
    apply Finset.sum_le_sum
    intro S _
    simpa only [S.property] using actual_supported_joint_card_le (q := q) S.val
  have hsum : (∑ S : {S : Finset (Fin n) // S.card = v},
      (3*v+18*v^2)^q) = n.choose v * (3*v+18*v^2)^q := by
    simp only [Finset.sum_const,Finset.card_univ,actual_vertex_sets_card,
      nsmul_eq_mul,Nat.cast_id]
  exact hc.trans (hs.trans (le_of_eq hsum))

theorem actual_joint_given_vertex_count_power_bound (n q v : ℕ) :
    Fintype.card {f : JointDatum n q // (VertexSupport (JointPattern f)).card = v} ≤
      n^v * (3*v+18*v^2)^q := by
  exact (actual_joint_given_vertex_count_card_le n q v).trans
    (Nat.mul_le_mul_right _ (Nat.choose_le_pow n v))

#print axioms actual_joint_given_vertex_count_power_bound

#print axioms actual_vertex_sets_card
#print axioms actual_joint_given_vertex_count_card_le
end Reference.MD06BadSupportEnumeration
