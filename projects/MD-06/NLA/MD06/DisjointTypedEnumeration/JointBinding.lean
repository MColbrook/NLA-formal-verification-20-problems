module

public import NLA.MD06.DisjointTypedEnumeration.TupleBijection
public import NLA.MD06.DisjointTypedEnumeration.JointDefinitions
public import NLA.MD06.BadDisjointDecomposition.Counts

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06JointSupportCounts
open Reference.MD06BadJointMoments Reference.MD06WeightedOverlap
open Reference.MD06BadDisjointDecomposition
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_typed_tuple_injective {n q : ℕ} (S : Finset (Fin n)) (b : Fin q → Bool)
    (f : TypedTuple S b) : Function.Injective f.val := by
  intro i j he
  by_contra hij
  have hn : 0 < (VertexSupport (BadPattern (f.val i))).card := by
    rw [actual_bad_vertex_count]
    cases IsDouble (f.val i) <;> norm_num
  obtain ⟨u,hu⟩ := Finset.card_pos.mp hn
  have hv : u ∈ VertexSupport (BadPattern (f.val j)) := by rw [←he];exact hu
  exact Finset.disjoint_left.mp (f.property.2.2 i j hij) hu hv

def typedJointEquiv {n q : ℕ} (S : Finset (Fin n)) (b : Fin q → Bool) :
    TypedTuple S b ≃ TypedJoint S b :=
  { toFun := fun f =>
      ⟨⟨f.val,actual_typed_tuple_injective S b f⟩,
        (actual_no_overlap_iff_vertex_disjoint _).mpr f.property.2.2,
        f.property.1,f.property.2.1⟩
    invFun := fun f => ⟨f.val,f.property.2.1,f.property.2.2,
      (actual_no_overlap_iff_vertex_disjoint f.val).mp f.property.1⟩
    left_inv := by intro f;rfl
    right_inv := by intro f;apply Subtype.ext;apply Function.Embedding.ext;intro i;rfl }

theorem actual_typed_joint_card (n q : ℕ) (S : Finset (Fin n)) (b : Fin q → Bool) :
    Fintype.card (TypedJoint S b) = 3^(Weight b)*S.card.descFactorial (Weight b) := by
  rw [←Fintype.card_congr (typedJointEquiv S b),actual_typed_tuple_card]

def jointFlagEquiv {n q : ℕ} (S : Finset (Fin n)) :
    DisjointJoint (q := q) S ≃ Σ b : Fin q → Bool,TypedJoint S b :=
  { toFun := fun f => ⟨(fun i => IsDouble (f.val i)),f.val,f.property.1,
      (fun _ => rfl),f.property.2⟩
    invFun := fun f => ⟨f.2.val,f.2.property.1,f.2.property.2.2⟩
    left_inv := by intro f;rfl
    right_inv := by
      rintro ⟨b,f⟩
      have hb : (fun i => IsDouble (f.val i)) = b := funext f.property.2.1
      exact Sigma.subtype_ext hb rfl }

theorem actual_disjoint_joint_card (n q : ℕ) (S : Finset (Fin n)) :
    Fintype.card (DisjointJoint (q := q) S) =
      ∑ b : Fin q → Bool,3^(Weight b)*S.card.descFactorial (Weight b) := by
  rw [Fintype.card_congr (jointFlagEquiv S),Fintype.card_sigma]
  simp_rw [actual_typed_joint_card]

#print axioms actual_typed_tuple_injective
#print axioms typedJointEquiv
#print axioms actual_typed_joint_card
#print axioms jointFlagEquiv
#print axioms actual_disjoint_joint_card
end Reference.MD06DisjointTypedEnumeration
