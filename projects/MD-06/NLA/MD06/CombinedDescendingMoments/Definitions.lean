module

public import NLA.MD06.MixedLowCycleBijections.Definitions
public import Mathlib.Tactic.DeriveFintype

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedPatternShapes Reference.MD06MixedLowCycleBijections
open Reference.MD06CanonicalCyclePatterns Reference.MD06CubicConfiguration

inductive MarkTag where
  | loop
  | double
  | cycle
  deriving DecidableEq

instance markTagFintype : Fintype MarkTag :=
  ⟨{.loop,.double,.cycle},by intro t;cases t <;> simp⟩

def TagLength (ell : ℕ) : MarkTag→ℕ
  | .loop => 1
  | .double => 2
  | .cycle => ell

abbrev TaggedDatum (n ell : ℕ) :=
  Σt : MarkTag,CanonicalCycleDatum n (TagLength ell t)

def typedTaggedEquiv (n ell : ℕ) : TypedDatum n ell ≃ TaggedDatum n ell :=
  { toFun := fun d => match d with
      | Sum.inl (Sum.inl C) => ⟨.loop,C⟩
      | Sum.inl (Sum.inr C) => ⟨.double,C⟩
      | Sum.inr C => ⟨.cycle,C⟩
    invFun := fun d => match d with
      | ⟨.loop,C⟩ => Sum.inl (Sum.inl C)
      | ⟨.double,C⟩ => Sum.inl (Sum.inr C)
      | ⟨.cycle,C⟩ => Sum.inr C
    left_inv := by
      intro d
      cases d with
      | inl b => cases b <;> rfl
      | inr C => rfl
    right_inv := by rintro ⟨t,C⟩;cases t <;> rfl }

def MarkedToTagged {n ell : ℕ} (d : MarkedDatum n ell) : TaggedDatum n ell :=
  typedTaggedEquiv n ell (TypedMap d)

def TaggedPattern {n ell : ℕ} (d : TaggedDatum n ell) : Finset (Dart n×Dart n) :=
  d.2.val
end Reference.MD06CombinedMoments
