module

public import NLA.MD06.DisjointTypedEnumeration.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06JointSupportCounts

abbrev HeadDatum {n : ℕ} (S : Finset (Fin n)) (b : Bool) :=
  {d : BadDatum n // IsDouble d = b ∧ VertexSupport (BadPattern d) ⊆ S}

def ChoiceTree (n : ℕ) :
    (q : ℕ) → (S : Finset (Fin n)) → (b : Fin q → Bool) → Type
  | 0,_,_ => PUnit
  | q+1,S,b =>
    Σ h : HeadDatum S (b 0),
      ChoiceTree n q (S \ VertexSupport (BadPattern h.val)) (Fin.tail b)

attribute [local instance] Classical.propDecidable

noncomputable instance choiceTreeFintype (n q : ℕ) (S : Finset (Fin n))
    (b : Fin q → Bool) : Fintype (ChoiceTree n q S b) := by
  induction q generalizing S with
  | zero => change Fintype PUnit;infer_instance
  | succ q ih =>
    letI : ∀ h : HeadDatum S (b 0),
        Fintype (ChoiceTree n q (S \ VertexSupport (BadPattern h.val)) (Fin.tail b)) :=
      fun h => ih (S \ VertexSupport (BadPattern h.val)) (Fin.tail b)
    change Fintype (Σ h : HeadDatum S (b 0),
      ChoiceTree n q (S \ VertexSupport (BadPattern h.val)) (Fin.tail b))
    infer_instance

#print axioms choiceTreeFintype
end Reference.MD06DisjointTypedEnumeration
