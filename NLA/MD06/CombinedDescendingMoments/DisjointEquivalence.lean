module

public import NLA.MD06.CombinedDescendingMoments.DisjointDefinitions
public import NLA.MD06.CombinedDescendingMoments.TagProperties

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedPatternShapes Reference.MD06CanonicalCyclePatterns
open Reference.MD06CanonicalDisjointTuples
attribute [local instance] Classical.propDecidable

theorem actual_disjoint_marked_tagged_pattern_equivalence {n : ℕ}
    (S : Finset (Fin n)) (q ell : ℕ) :
    ∃E : DisjointMarkedTuple S q ell ≃ TaggedCycleTuple S q ell,
      ∀F,TupleUnion (E F).2=MarkedUnion F.val := by
  let E : MarkedDatum n ell ≃ TaggedDatum n ell :=
    Equiv.ofBijective MarkedToTagged (actual_marked_to_tagged_bijective n ell)
  have hpat (x : TaggedDatum n ell) : MarkedPattern (E.symm x)=x.2.val := by
    have h := actual_marked_to_tagged_pattern (E.symm x)
    change TaggedPattern (E (E.symm x))=MarkedPattern (E.symm x) at h
    rw [E.apply_symm_apply] at h
    exact h.symm
  let forward : DisjointMarkedTuple S q ell→TaggedCycleTuple S q ell := fun F =>
    ⟨fun i => (E (F.val i)).1,
      ⟨fun i => MarkedPattern (F.val i),
        (by intro i;dsimp only;rw [←actual_marked_to_tagged_pattern (F.val i)];exact (E (F.val i)).2.property),
        F.property.1,F.property.2⟩⟩
  let backward : TaggedCycleTuple S q ell→DisjointMarkedTuple S q ell := fun F =>
    ⟨fun i => E.symm ⟨F.1 i,⟨F.2.val i,F.2.property.1 i⟩⟩,
      (by intro i;rw [hpat];exact F.2.property.2.1 i),
      (by intro i j hij;rw [hpat,hpat];exact F.2.property.2.2 i j hij)⟩
  let equiv : DisjointMarkedTuple S q ell ≃ TaggedCycleTuple S q ell :=
    { toFun := forward
      invFun := backward
      left_inv := by
        intro F
        apply Subtype.ext
        funext i
        dsimp only [forward,backward]
        apply E.injective
        rw [E.apply_symm_apply]
        apply Sigma.subtype_ext
        · rfl
        · exact (actual_marked_to_tagged_pattern (F.val i)).symm
      right_inv := by
        intro F
        apply Sigma.subtype_ext
        · funext i
          dsimp only [forward,backward]
          exact congrArg Sigma.fst (E.apply_symm_apply ⟨F.1 i,⟨F.2.val i,F.2.property.1 i⟩⟩)
        · funext i
          dsimp only [forward,backward]
          exact hpat ⟨F.1 i,⟨F.2.val i,F.2.property.1 i⟩⟩ }
  refine ⟨equiv,?_⟩
  intro F
  rfl

#print axioms actual_disjoint_marked_tagged_pattern_equivalence
end Reference.MD06CombinedMoments
