module

public import NLA.MD06.CanonicalDisjointTuples.HeadTailDefinitions
public import NLA.MD06.SupportedCanonicalCycles.TreeCardinality

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalDisjointTuples
open Reference.MD06SupportedCanonicalCycles
attribute [local instance] Classical.propDecidable

theorem actual_canonical_disjoint_tuple_scaled_card (n q : ℕ) (S : Finset (Fin n))
    (L : Fin q→ℕ) (hL : ∀i,0<L i) :
    CycleSymmetryFactor L*Fintype.card (CanonicalTuple S L)=
      S.card.descFactorial (CycleWeight L)*6^(CycleWeight L) := by
  rw [Fintype.card_congr (canonicalChoiceEquiv n q S L)]
  exact actual_canonical_choice_tree_scaled_card n q S L hL

#print axioms actual_canonical_disjoint_tuple_scaled_card
end Reference.MD06CanonicalDisjointTuples
