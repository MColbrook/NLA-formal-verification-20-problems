module

public import NLA.MD06.BadSupportEnumeration.Cardinality

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadSupportEnumeration
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
open Reference.MD06BadJointMoments Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

theorem actual_vertex_support_mono {n : ℕ} {C D : Finset (Dart n × Dart n)}
    (h : C ⊆ D) : VertexSupport C ⊆ VertexSupport D := by
  intro u hu
  obtain ⟨a,ha⟩ := (actual_mem_vertex_support C u).mp hu
  exact (actual_mem_vertex_support D u).mpr ⟨a,actual_dart_support_mono h ha⟩

theorem actual_supported_joint_component {n q : ℕ} (S : Finset (Fin n))
    (f : SupportedJointDatum n q S) (i : Fin q) :
    VertexSupport (BadPattern (f.val i)) ⊆ S := by
  apply Finset.Subset.trans _ f.property
  apply actual_vertex_support_mono
  intro e he
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,he⟩

theorem actual_supported_joint_card_le {n q : ℕ} (S : Finset (Fin n)) :
    Fintype.card (SupportedJointDatum n q S) ≤ (3*S.card+18*S.card^2)^q := by
  let encode : SupportedJointDatum n q S → Fin q → SupportedBadDatum n S :=
    fun f i => ⟨f.val i,actual_supported_joint_component S f i⟩
  have hi : Function.Injective encode := by
    intro f g h
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    exact congrArg Subtype.val (congrFun h i)
  have hc := Fintype.card_le_of_injective encode hi
  have hpow := Nat.pow_le_pow_left (actual_supported_bad_card_le S) q
  calc
    Fintype.card (SupportedJointDatum n q S) ≤
        Fintype.card (Fin q → SupportedBadDatum n S) := hc
    _ = (Fintype.card (SupportedBadDatum n S))^q := by simp
    _ ≤ (3*S.card+18*S.card^2)^q := hpow

#print axioms actual_vertex_support_mono
#print axioms actual_supported_joint_component
#print axioms actual_supported_joint_card_le
end Reference.MD06BadSupportEnumeration
