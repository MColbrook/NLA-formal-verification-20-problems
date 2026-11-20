module

public import NLA.MD06.CanonicalDisjointTuples.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalDisjointTuples
open Reference.MD06CanonicalCyclePatterns Reference.MD06SupportedCanonicalCycles
open Reference.MD06CyclePairPatterns Reference.MD06CubicConfiguration Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

def canonicalHead {n q : ℕ} (S : Finset (Fin n)) (L : Fin (q+1)→ℕ)
    (F : CanonicalTuple S L) : SupportedCanonicalCycle S (L 0) :=
  ⟨⟨F.val 0,F.property.1 0⟩,F.property.2.1 0⟩

def canonicalTail {n q : ℕ} (S : Finset (Fin n)) (L : Fin (q+1)→ℕ)
    (F : CanonicalTuple S L) :
    CanonicalTuple (S\VertexSupport (canonicalHead S L F).val.val) (Fin.tail L) := by
  refine ⟨Fin.tail F.val,?_,?_,?_⟩
  · exact fun i => F.property.1 i.succ
  · intro i x hx
    apply Finset.mem_sdiff.mpr
    refine ⟨F.property.2.1 i.succ hx,?_⟩
    exact fun hy => Finset.disjoint_left.mp
      (F.property.2.2 i.succ 0 (Fin.succ_ne_zero i)) hx hy
  · intro i j hij
    exact F.property.2.2 i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))

def canonicalCons {n q : ℕ} (S : Finset (Fin n)) (L : Fin (q+1)→ℕ)
    (h : SupportedCanonicalCycle S (L 0))
    (t : CanonicalTuple (S\VertexSupport h.val.val) (Fin.tail L)) :
    CanonicalTuple S L := by
  refine ⟨Fin.cons h.val.val t.val,?_,?_,?_⟩
  · intro i
    refine Fin.cases h.val.property (fun j => t.property.1 j) i
  · intro i
    refine Fin.cases h.property (fun j x hx => (Finset.mem_sdiff.mp (t.property.2.1 j hx)).1) i
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

def canonicalHeadTailEquiv {n q : ℕ} (S : Finset (Fin n)) (L : Fin (q+1)→ℕ) :
    CanonicalTuple S L ≃
      Σ h : SupportedCanonicalCycle S (L 0),
        CanonicalTuple (S\VertexSupport h.val.val) (Fin.tail L) :=
  { toFun := fun F => ⟨canonicalHead S L F,canonicalTail S L F⟩
    invFun := fun F => canonicalCons S L F.1 F.2
    left_inv := by
      intro F
      apply Subtype.ext
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    right_inv := by rintro ⟨h,t⟩;rfl }

def canonicalZeroEquiv {n : ℕ} (S : Finset (Fin n)) (L : Fin 0→ℕ) :
    CanonicalTuple S L ≃ PUnit :=
  { toFun := fun _ => PUnit.unit
    invFun := fun _ => ⟨Fin.elim0,by intro i;exact Fin.elim0 i,
      by intro i;exact Fin.elim0 i,by intro i;exact Fin.elim0 i⟩
    left_inv := by intro F;apply Subtype.ext;funext i;exact Fin.elim0 i
    right_inv := by intro F;cases F;rfl }

def canonicalChoiceEquiv (n q : ℕ) (S : Finset (Fin n)) (L : Fin q→ℕ) :
    CanonicalTuple S L ≃ CanonicalChoiceTree n q S L := by
  induction q generalizing S with
  | zero => exact canonicalZeroEquiv S L
  | succ q ih =>
    exact (canonicalHeadTailEquiv S L).trans
      (Equiv.sigmaCongrRight (fun h => ih
        (S\VertexSupport h.val.val) (Fin.tail L)))

#print axioms canonicalHead
#print axioms canonicalTail
#print axioms canonicalCons
#print axioms canonicalHeadTailEquiv
#print axioms canonicalZeroEquiv
#print axioms canonicalChoiceEquiv
end Reference.MD06CanonicalDisjointTuples
