module

public import NLA.MD06.DisjointTypedEnumeration.TreeCardinality

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06JointSupportCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def typedHead {n q : ℕ} (S : Finset (Fin n)) (b : Fin (q+1) → Bool)
    (f : TypedTuple S b) : HeadDatum S (b 0) :=
  ⟨f.val 0,f.property.1 0,f.property.2.1 0⟩

def typedTail {n q : ℕ} (S : Finset (Fin n)) (b : Fin (q+1) → Bool)
    (f : TypedTuple S b) :
    TypedTuple (S \ VertexSupport (BadPattern (typedHead S b f).val)) (Fin.tail b) := by
  refine ⟨Fin.tail f.val,?_,?_,?_⟩
  · exact fun i => f.property.1 i.succ
  · intro i x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨f.property.2.1 i.succ hx,?_⟩
    exact fun hy => Finset.disjoint_left.mp
      (f.property.2.2 i.succ 0 (Fin.succ_ne_zero i)) hx hy
  · intro i j hij
    exact f.property.2.2 i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))

def typedCons {n q : ℕ} (S : Finset (Fin n)) (b : Fin (q+1) → Bool)
    (h : HeadDatum S (b 0))
    (t : TypedTuple (S \ VertexSupport (BadPattern h.val)) (Fin.tail b)) :
    TypedTuple S b := by
  refine ⟨Fin.cons h.val t.val,?_,?_,?_⟩
  · intro i
    refine Fin.cases h.property.1 (fun j => t.property.1 j) i
  · intro i
    refine Fin.cases h.property.2 (fun j x hx => (Finset.mem_sdiff.mp (t.property.2.1 j hx)).1) i
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun a => ?_) j
      · intro hij;exact (hij rfl).elim
      · intro _;apply Finset.disjoint_left.mpr
        intro x hx hy
        exact (Finset.mem_sdiff.mp (t.property.2.1 a hy)).2 hx
    · refine Fin.cases ?_ (fun c => ?_) j
      · intro _;apply Finset.disjoint_left.mpr
        intro x hx hy
        exact (Finset.mem_sdiff.mp (t.property.2.1 a hx)).2 hy
      · intro hij;exact t.property.2.2 a c (fun hh => hij (congrArg Fin.succ hh))

def typedHeadTailEquiv {n q : ℕ} (S : Finset (Fin n)) (b : Fin (q+1) → Bool) :
    TypedTuple S b ≃
      Σ h : HeadDatum S (b 0),
        TypedTuple (S \ VertexSupport (BadPattern h.val)) (Fin.tail b) :=
  { toFun := fun f => ⟨typedHead S b f,typedTail S b f⟩
    invFun := fun f => typedCons S b f.1 f.2
    left_inv := by
      intro f
      apply Subtype.ext
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    right_inv := by
      rintro ⟨h,t⟩
      rfl }

def typedZeroEquiv {n : ℕ} (S : Finset (Fin n)) (b : Fin 0 → Bool) :
    TypedTuple S b ≃ PUnit :=
  { toFun := fun _ => PUnit.unit
    invFun := fun _ => ⟨Fin.elim0,by intro i;exact Fin.elim0 i,
      by intro i;exact Fin.elim0 i,by intro i;exact Fin.elim0 i⟩
    left_inv := by intro f;apply Subtype.ext;funext i;exact Fin.elim0 i
    right_inv := by intro f;cases f;rfl }

def typedChoiceEquiv (n q : ℕ) (S : Finset (Fin n)) (b : Fin q → Bool) :
    TypedTuple S b ≃ ChoiceTree n q S b := by
  induction q generalizing S with
  | zero => exact typedZeroEquiv S b
  | succ q ih =>
    exact (typedHeadTailEquiv S b).trans
      (Equiv.sigmaCongrRight (fun h => ih
        (S \ VertexSupport (BadPattern h.val)) (Fin.tail b)))

theorem actual_typed_tuple_card (n q : ℕ) (S : Finset (Fin n)) (b : Fin q → Bool) :
    Fintype.card (TypedTuple S b) = 3^(Weight b)*S.card.descFactorial (Weight b) := by
  rw [Fintype.card_congr (typedChoiceEquiv n q S b),actual_choice_tree_card]

#print axioms typedHead
#print axioms typedTail
#print axioms typedCons
#print axioms typedHeadTailEquiv
#print axioms typedZeroEquiv
#print axioms typedChoiceEquiv
#print axioms actual_typed_tuple_card
end Reference.MD06DisjointTypedEnumeration
