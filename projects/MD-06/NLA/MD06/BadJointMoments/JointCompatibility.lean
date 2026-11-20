module

public import NLA.MD06.BadJointMoments.OrderDefinitions
public import NLA.MD06.PairingCounts.PatternProduct

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadJointMoments
open Reference.MD06Simplicity Reference.MD06CubicConfiguration Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

theorem actual_dart_lt_asymm {n : ℕ} {x y : Dart n} (h : DartLT x y) :
    ¬ DartLT y x := by
  rcases h with h | ⟨h,h'⟩
  · rintro (g | ⟨g,g'⟩) <;> omega
  · rintro (g | ⟨g,g'⟩) <;> omega

theorem actual_bad_pattern_ordered {n : ℕ} (z : BadDatum n) :
    ∀ e ∈ BadPattern z, DartLT e.1 e.2 := by
  cases z with
  | inl d =>
    intro e he
    have heq : e = ((d.1,d.2.val.1),(d.1,d.2.val.2)) := by
      simpa only [BadPattern,LoopPattern,Finset.mem_singleton] using he
    subst e
    exact Or.inr ⟨rfl,d.2.property⟩
  | inr d =>
    intro e he
    simp only [BadPattern] at he
    unfold DoublePattern at he
    split at he <;> simp only [Finset.mem_insert,Finset.mem_singleton] at he <;>
      rcases he with rfl | rfl <;> exact Or.inl d.1.property

theorem actual_joint_pattern_ordered {n q : ℕ} (f : JointDatum n q) :
    ∀ e ∈ JointPattern f, DartLT e.1 e.2 := by
  intro e he
  rcases Finset.mem_biUnion.mp he with ⟨i,hi,he⟩
  exact actual_bad_pattern_ordered (f i) e he

theorem actual_ordered_matching_constraints_disjoint {n : ℕ}
    (C : Finset (Dart n × Dart n)) (p : Pairing n)
    (ho : ∀ e ∈ C, DartLT e.1 e.2) (hm : Matches C p) :
    ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  have hi (e : Dart n × Dart n) (he : e ∈ C) : p.val e.2 = e.1 := by
    have h := p.property.1 e.1
    rw [hm e he] at h
    exact h
  intro e he f hf hef
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have h1 : e.1 = f.1 := hx.symm.trans hy
    have h2 : e.2 = f.2 := (hm e he).symm.trans
      ((congrArg p.val h1).trans (hm f hf))
    exact hef (Prod.ext h1 h2)
  · have h1 : e.1 = f.2 := hx.symm.trans hy
    have h2 : e.2 = f.1 := (hm e he).symm.trans
      ((congrArg p.val h1).trans (hi f hf))
    exact (actual_dart_lt_asymm (ho e he))
      (by simpa only [← h1,← h2] using ho f hf)
  · have h2 : e.2 = f.1 := hx.symm.trans hy
    have h1 : e.1 = f.2 := (hi e he).symm.trans
      ((congrArg p.val h2).trans (hm f hf))
    exact (actual_dart_lt_asymm (ho e he))
      (by simpa only [← h1,← h2] using ho f hf)
  · have h2 : e.2 = f.2 := hx.symm.trans hy
    have h1 : e.1 = f.1 := (hi e he).symm.trans
      ((congrArg p.val h2).trans (hi f hf))
    exact hef (Prod.ext h1 h2)

theorem actual_joint_pattern_distinct_endpoints {n q : ℕ} (f : JointDatum n q) :
    ∀ e ∈ JointPattern f, e.1 ≠ e.2 := by
  intro e he h
  have ho := actual_joint_pattern_ordered f e he
  exact (actual_dart_lt_asymm ho) (by simpa only [h] using ho)

theorem actual_joint_matching_disjoint_endpoints {n q : ℕ}
    (f : JointDatum n q) (p : Pairing n) (hm : Matches (JointPattern f) p) :
    ∀ e ∈ JointPattern f, ∀ g ∈ JointPattern f, e ≠ g →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {g.1,g.2} := by
  exact actual_ordered_matching_constraints_disjoint (JointPattern f) p
    (actual_joint_pattern_ordered f) hm

theorem actual_joint_pattern_count_product_or_zero {n q : ℕ} (f : JointDatum n q) :
    PatternCount (JointPattern f) = 0 ∨
      PatternCount (JointPattern f) * PairingDenominator n (JointPattern f).card =
        Fintype.card (Pairing n) := by
  by_cases hz : PatternCount (JointPattern f) = 0
  · exact Or.inl hz
  · have hc : Fintype.card {p : Pairing n // Matches (JointPattern f) p} ≠ 0 := by
      simpa only [PatternCount,← Nat.card_eq_fintype_card] using hz
    have hp : Nonempty {p : Pairing n // Matches (JointPattern f) p} :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hc)
    obtain ⟨p,hp⟩ := hp
    exact Or.inr (actual_disjoint_pattern_count_product (JointPattern f)
      (actual_joint_pattern_distinct_endpoints f)
      (actual_joint_matching_disjoint_endpoints f p hp))

#print axioms actual_dart_lt_asymm
#print axioms actual_bad_pattern_ordered
#print axioms actual_joint_pattern_ordered
#print axioms actual_ordered_matching_constraints_disjoint
#print axioms actual_joint_pattern_distinct_endpoints
#print axioms actual_joint_matching_disjoint_endpoints
#print axioms actual_joint_pattern_count_product_or_zero
end Reference.MD06BadJointMoments
