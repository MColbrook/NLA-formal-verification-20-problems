module

public import NLA.MD06.SupportedCanonicalCycles.HeadProperties
public import NLA.MD06.SupportedCanonicalCycles.Cardinality

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06SupportedCanonicalCycles
open Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

theorem actual_canonical_choice_tree_scaled_card (n q : ℕ) (S : Finset (Fin n))
    (L : Fin q→ℕ) (hL : ∀i,0<L i) :
    CycleSymmetryFactor L*Fintype.card (CanonicalChoiceTree n q S L)=
      S.card.descFactorial (CycleWeight L)*6^(CycleWeight L) := by
  induction q generalizing S with
  | zero =>
    simp [CanonicalChoiceTree,CycleWeight,CycleSymmetryFactor]
  | succ q ih =>
    let t : ℕ := L 0
    let w : ℕ := CycleWeight (Fin.tail L)
    let f : ℕ := CycleSymmetryFactor (Fin.tail L)
    let := NeZero.of_pos (hL 0)
    have htail : ∀i,0<(Fin.tail L) i := fun i => hL i.succ
    have hdesc : S.card.descFactorial t*(S.card-t).descFactorial w=
        S.card.descFactorial (t+w) := by
      have h := Nat.descFactorial_mul_descFactorial
        (n := S.card) (k := t) (m := t+w) (by omega : t≤t+w)
      simpa only [Nat.add_sub_cancel_left,Nat.mul_comm] using h
    have hsum : f*Fintype.card (CanonicalChoiceTree n (q+1) S L)=
        Fintype.card (SupportedCanonicalCycle S (L 0))*
          ((S.card-t).descFactorial w*6^w) := by
      change f*Fintype.card (Σ C : SupportedCanonicalCycle S (L 0),
        CanonicalChoiceTree n q (S\VertexSupport C.val.val) (Fin.tail L))=_
      rw [Fintype.card_sigma,Finset.mul_sum]
      have hc (C : SupportedCanonicalCycle S (L 0)) :
          f*Fintype.card (CanonicalChoiceTree n q
            (S\VertexSupport C.val.val) (Fin.tail L))=
          (S.card-t).descFactorial w*6^w := by
        rw [ih _ (Fin.tail L) htail,actual_cycle_head_remaining_card]
      simp_rw [hc]
      simp
    rw [actual_cycle_factor_succ,actual_cycle_weight_succ]
    change ((2*t)*f)*Fintype.card (CanonicalChoiceTree n (q+1) S L)=
      S.card.descFactorial (t+w)*6^(t+w)
    calc
      ((2*t)*f)*Fintype.card (CanonicalChoiceTree n (q+1) S L)=
          (2*t)*(f*Fintype.card (CanonicalChoiceTree n (q+1) S L)) := by ring
      _ = (2*t)*(Fintype.card (SupportedCanonicalCycle S (L 0))*
          ((S.card-t).descFactorial w*6^w)) := by rw [hsum]
      _ = ((2*t)*Fintype.card (SupportedCanonicalCycle S (L 0)))*
          ((S.card-t).descFactorial w*6^w) := by ring
      _ = (S.card.descFactorial t*6^t)*((S.card-t).descFactorial w*6^w) := by
        rw [actual_supported_canonical_cycle_card]
      _ = S.card.descFactorial (t+w)*6^(t+w) := by rw [pow_add,←hdesc];ring

#print axioms actual_canonical_choice_tree_scaled_card
end Reference.MD06SupportedCanonicalCycles
