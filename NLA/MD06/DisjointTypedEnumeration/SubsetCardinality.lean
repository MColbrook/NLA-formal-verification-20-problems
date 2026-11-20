module

public import NLA.MD06.DisjointTypedEnumeration.Definitions
public import NLA.MD06.JointSupportCounts.BadSupport
public import NLA.MD06.BadPatternCounts.Cardinality
public import Mathlib.Data.Finset.Sort

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06CubicConfiguration Reference.MD06JointSupportCounts
open Reference.MD06BadPatternCounts
attribute [local instance] Classical.propDecidable

theorem actual_vertex_pair_card {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (VertexPair S) = S.card.choose 2 := by
  let o := S.orderIsoOfFin rfl
  let equiv : {uv : Fin S.card × Fin S.card // uv.1 < uv.2} ≃ VertexPair S :=
    { toFun := fun x => ⟨(o x.val.1,o x.val.2),o.lt_iff_lt.mpr x.property⟩
      invFun := fun x => ⟨(o.symm x.val.1,o.symm x.val.2),
        o.symm.lt_iff_lt.mpr x.property⟩
      left_inv := by
        rintro ⟨⟨u,v⟩,h⟩
        apply Subtype.ext
        exact Prod.ext (o.symm_apply_apply u) (o.symm_apply_apply v)
      right_inv := by
        rintro ⟨⟨u,v⟩,h⟩
        apply Subtype.ext
        exact Prod.ext (o.apply_symm_apply u) (o.apply_symm_apply v) }
  have h := Fintype.card_congr equiv
  rw [actual_strict_vertex_pair_card] at h
  exact h.symm

theorem actual_supported_loop_card {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (SupportedLoop S) = 3*S.card := by
  let equiv : SupportedLoop S ≃ (↥S × OrderedLocalPair) :=
    { toFun := fun x => (⟨x.val.1,x.property (by
        simp [actual_loop_vertex_support])⟩,x.val.2)
      invFun := fun x => ⟨(x.1.val,x.2),by
        intro u hu
        simp only [actual_loop_vertex_support,Finset.mem_singleton] at hu
        subst u
        exact x.1.property⟩
      left_inv := by rintro ⟨⟨u,a⟩,h⟩;rfl
      right_inv := by rintro ⟨⟨u,h⟩,a⟩;rfl }
  rw [Fintype.card_congr equiv,Fintype.card_prod,Fintype.card_coe,
    actual_ordered_local_pair_card]
  omega

theorem actual_double_vertex_support {n : ℕ} (d : DoubleDatum n) :
    VertexSupport (DoublePattern d) = {d.1.val.1,d.1.val.2} := by
  cases hb : d.2.2.2 <;>
    simp only [DoublePattern,hb,Bool.false_eq_true,if_false,if_true,
      actual_two_edge_vertex_support]

theorem actual_supported_double_card {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (SupportedDouble S) = 18*S.card.choose 2 := by
  let equiv : SupportedDouble S ≃
      (VertexPair S × OrderedLocalPair × OrderedLocalPair × Bool) :=
    { toFun := fun x =>
        (⟨(⟨x.val.1.val.1,x.property (by simp [actual_double_vertex_support])⟩,
            ⟨x.val.1.val.2,x.property (by simp [actual_double_vertex_support])⟩),
          x.val.1.property⟩,x.val.2)
      invFun := fun x =>
        ⟨(⟨(x.1.val.1.val,x.1.val.2.val),x.1.property⟩,x.2),by
          intro u hu
          rw [actual_double_vertex_support] at hu
          simp only [Finset.mem_insert,Finset.mem_singleton] at hu
          rcases hu with hu | hu
          · subst u;exact x.1.val.1.property
          · subst u;exact x.1.val.2.property⟩
      left_inv := by rintro ⟨⟨⟨⟨u,v⟩,huv⟩,a,b,h⟩,hs⟩;rfl
      right_inv := by rintro ⟨⟨⟨⟨u,hu⟩,⟨v,hv⟩⟩,huv⟩,a,b,h⟩;rfl }
  rw [Fintype.card_congr equiv]
  simp only [Fintype.card_prod,actual_vertex_pair_card,actual_ordered_local_pair_card,
    Fintype.card_bool]
  ring

#print axioms actual_vertex_pair_card
#print axioms actual_supported_loop_card
#print axioms actual_double_vertex_support
#print axioms actual_supported_double_card
end Reference.MD06DisjointTypedEnumeration
