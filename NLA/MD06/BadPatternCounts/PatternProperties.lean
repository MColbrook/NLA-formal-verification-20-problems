module

public import NLA.MD06.SimplicityBonferroni.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadPatternCounts
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
attribute [local instance] Classical.propDecidable

theorem actual_two_edge_card {n : ℕ} (u v : Fin n) (a b c d : Fin 3)
    (hab : a ≠ b) :
    ({((u,a),(v,c)),((u,b),(v,d))} : Finset (Dart n × Dart n)).card = 2 := by
  have h : ((u,a),(v,c)) ≠ ((u,b),(v,d)) := by
    intro h
    exact hab (congrArg (fun x => x.1.2) h)
  simp [h]

theorem actual_two_edge_distinct_endpoints {n : ℕ} (u v : Fin n)
    (a b c d : Fin 3) (huv : u ≠ v) :
    ∀ e ∈ ({((u,a),(v,c)),((u,b),(v,d))} : Finset (Dart n × Dart n)),
      e.1 ≠ e.2 := by
  intro e he
  simp only [Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl <;>
    exact fun h => huv (congrArg Prod.fst h)

theorem actual_source_target_support_disjoint {n : ℕ} (u v : Fin n)
    (a b c d : Fin 3) (huv : u ≠ v) (hab : a ≠ b) (hcd : c ≠ d) :
    Disjoint ({(u,a),(v,c)} : Finset (Dart n)) {(u,b),(v,d)} := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hab (congrArg Prod.snd (hx.symm.trans hy))
  · exact huv (congrArg Prod.fst (hx.symm.trans hy))
  · exact huv (congrArg Prod.fst (hy.symm.trans hx))
  · exact hcd (congrArg Prod.snd (hx.symm.trans hy))

theorem actual_two_edge_disjoint_endpoints {n : ℕ} (u v : Fin n)
    (a b c d : Fin 3) (huv : u ≠ v) (hab : a ≠ b) (hcd : c ≠ d) :
    ∀ e ∈ ({((u,a),(v,c)),((u,b),(v,d))} : Finset (Dart n × Dart n)),
      ∀ f ∈ ({((u,a),(v,c)),((u,b),(v,d))} : Finset (Dart n × Dart n)), e ≠ f →
        Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  intro e he f hf hef
  simp only [Finset.mem_insert,Finset.mem_singleton] at he hf
  rcases he with rfl | rfl <;> rcases hf with rfl | rfl
  · exact (hef rfl).elim
  · exact actual_source_target_support_disjoint u v a b c d huv hab hcd
  · exact (actual_source_target_support_disjoint u v a b c d huv hab hcd).symm
  · exact (hef rfl).elim

theorem actual_loop_pattern_card {n : ℕ} (d : LoopDatum n) :
    (LoopPattern d).card = 1 := by simp [LoopPattern]

theorem actual_loop_pattern_distinct_endpoints {n : ℕ} (d : LoopDatum n) :
    ∀ e ∈ LoopPattern d, e.1 ≠ e.2 := by
  intro e he
  have heq : e = ((d.1,d.2.val.1),(d.1,d.2.val.2)) := by simpa [LoopPattern] using he
  subst e
  exact fun h => (ne_of_lt d.2.property) (congrArg Prod.snd h)

theorem actual_loop_pattern_disjoint_endpoints {n : ℕ} (d : LoopDatum n) :
    ∀ e ∈ LoopPattern d, ∀ f ∈ LoopPattern d, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  intro e he f hf hef
  have heq : e = ((d.1,d.2.val.1),(d.1,d.2.val.2)) := by simpa [LoopPattern] using he
  have hfq : f = ((d.1,d.2.val.1),(d.1,d.2.val.2)) := by simpa [LoopPattern] using hf
  exact (hef (heq.trans hfq.symm)).elim

theorem actual_double_pattern_card {n : ℕ} (d : DoubleDatum n) :
    (DoublePattern d).card = 2 := by
  cases hb : d.2.2.2 with
  | false =>
    simpa only [DoublePattern,hb,Bool.false_eq_true,if_false] using
      actual_two_edge_card d.1.val.1 d.1.val.2 d.2.1.val.1 d.2.1.val.2
        d.2.2.1.val.1 d.2.2.1.val.2 (ne_of_lt d.2.1.property)
  | true =>
    simpa only [DoublePattern,hb,if_true] using
      actual_two_edge_card d.1.val.1 d.1.val.2 d.2.1.val.1 d.2.1.val.2
        d.2.2.1.val.2 d.2.2.1.val.1 (ne_of_lt d.2.1.property)

theorem actual_double_pattern_distinct_endpoints {n : ℕ} (d : DoubleDatum n) :
    ∀ e ∈ DoublePattern d, e.1 ≠ e.2 := by
  cases hb : d.2.2.2 with
  | false =>
    simpa only [DoublePattern,hb,Bool.false_eq_true,if_false] using
      actual_two_edge_distinct_endpoints d.1.val.1 d.1.val.2 d.2.1.val.1 d.2.1.val.2
        d.2.2.1.val.1 d.2.2.1.val.2 (ne_of_lt d.1.property)
  | true =>
    simpa only [DoublePattern,hb,if_true] using
      actual_two_edge_distinct_endpoints d.1.val.1 d.1.val.2 d.2.1.val.1 d.2.1.val.2
        d.2.2.1.val.2 d.2.2.1.val.1 (ne_of_lt d.1.property)

theorem actual_double_pattern_disjoint_endpoints {n : ℕ} (d : DoubleDatum n) :
    ∀ e ∈ DoublePattern d, ∀ f ∈ DoublePattern d, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  cases hb : d.2.2.2 with
  | false =>
    simpa only [DoublePattern,hb,Bool.false_eq_true,if_false] using
      actual_two_edge_disjoint_endpoints d.1.val.1 d.1.val.2 d.2.1.val.1 d.2.1.val.2
        d.2.2.1.val.1 d.2.2.1.val.2 (ne_of_lt d.1.property)
        (ne_of_lt d.2.1.property) (ne_of_lt d.2.2.1.property)
  | true =>
    simpa only [DoublePattern,hb,if_true] using
      actual_two_edge_disjoint_endpoints d.1.val.1 d.1.val.2 d.2.1.val.1 d.2.1.val.2
        d.2.2.1.val.2 d.2.2.1.val.1 (ne_of_lt d.1.property)
        (ne_of_lt d.2.1.property) (ne_of_lt d.2.2.1.property).symm

#print axioms actual_two_edge_card
#print axioms actual_two_edge_distinct_endpoints
#print axioms actual_source_target_support_disjoint
#print axioms actual_two_edge_disjoint_endpoints
#print axioms actual_loop_pattern_card
#print axioms actual_loop_pattern_distinct_endpoints
#print axioms actual_loop_pattern_disjoint_endpoints
#print axioms actual_double_pattern_card
#print axioms actual_double_pattern_distinct_endpoints
#print axioms actual_double_pattern_disjoint_endpoints
end Reference.MD06BadPatternCounts