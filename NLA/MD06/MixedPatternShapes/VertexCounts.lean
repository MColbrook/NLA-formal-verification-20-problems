module

public import NLA.MD06.MixedPatternShapes.MarkedCounts
public import NLA.MD06.BadSupportEnumeration.VertexCounts

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedPatternShapes
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
open Reference.MD06Simplicity Reference.MD06SupportedCanonicalCycles
open Reference.MD06BadSupportEnumeration
attribute [local instance] Classical.propDecidable

theorem actual_marked_given_vertex_card_bound (n q ell v : ℕ) :
    Fintype.card {F : MarkedTuple n q ell // (VertexSupport (MarkedUnion F)).card=v}≤
      n.choose v*(3*v+18*v^2+2^(9*v^2))^q := by
  let f : {F : MarkedTuple n q ell // (VertexSupport (MarkedUnion F)).card=v}→
      (Σ S : {S : Finset (Fin n) // S.card=v},SupportedMarkedTuple S.val q ell) :=
    fun F => ⟨⟨VertexSupport (MarkedUnion F.val),F.property⟩,
      ⟨F.val,Finset.Subset.refl _⟩⟩
  have hf : Function.Injective f := by
    intro F G h
    apply Subtype.ext
    exact congrArg (fun z => z.2.val) h
  have hc := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at hc
  have hs : (∑ S : {S : Finset (Fin n) // S.card=v},
      Fintype.card (SupportedMarkedTuple S.val q ell))≤
        ∑ S : {S : Finset (Fin n) // S.card=v},(3*v+18*v^2+2^(9*v^2))^q := by
    apply Finset.sum_le_sum
    intro S _
    simpa only [S.property] using actual_supported_marked_tuple_card_bound (q := q) (ell := ell) S.val
  have hsum : (∑ S : {S : Finset (Fin n) // S.card=v},(3*v+18*v^2+2^(9*v^2))^q)=
      n.choose v*(3*v+18*v^2+2^(9*v^2))^q := by
    simp only [Finset.sum_const,Finset.card_univ,actual_vertex_sets_card,nsmul_eq_mul,Nat.cast_id]
  exact hc.trans (hs.trans (le_of_eq hsum))

theorem actual_marked_given_vertex_power_bound (n q ell v : ℕ) :
    Fintype.card {F : MarkedTuple n q ell // (VertexSupport (MarkedUnion F)).card=v}≤
      n^v*(3*v+18*v^2+2^(9*v^2))^q := by
  exact (actual_marked_given_vertex_card_bound n q ell v).trans
    (Nat.mul_le_mul_right _ (Nat.choose_le_pow n v))

#print axioms actual_marked_given_vertex_card_bound
#print axioms actual_marked_given_vertex_power_bound
end Reference.MD06MixedPatternShapes
