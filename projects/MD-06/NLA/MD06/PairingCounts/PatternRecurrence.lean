module

public import NLA.MD06.PairingCounts.PatternSymmetry

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06PairingCounts
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_constrained_mate_sum {n : ℕ} (C : Finset (Dart n × Dart n))
    (a : Dart n) :
    (∑ b : Dart n, ConstrainedMateCount C a b) = PatternCount C := by
  let e : (Σ b : Dart n, {p : Pairing n // Matches C p ∧ p.val a = b}) ≃
      {p : Pairing n // Matches C p} :=
    { toFun := fun x => ⟨x.2.val,x.2.property.1⟩
      invFun := fun p => ⟨p.val.val a,⟨p.val,p.property,rfl⟩⟩
      left_inv := by rintro ⟨b,p,hp,h⟩; subst b; rfl
      right_inv := by intro p; rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma] at h
  exact h

theorem actual_constrained_mate_zero_forbidden {n : ℕ}
    (C : Finset (Dart n × Dart n)) (a b : Dart n) (ha : a ∉ UsedDarts C)
    (hb : b ∈ insert a (UsedDarts C)) :
    ConstrainedMateCount C a b = 0 := by
  unfold ConstrainedMateCount
  have : IsEmpty {p : Pairing n // Matches C p ∧ p.val a = b} := by
    constructor
    intro p
    rcases Finset.mem_insert.mp hb with hba | hbu
    · exact p.val.property.2 a (p.property.2.trans hba)
    · have ho := actual_matching_partner_outside C p.val p.property.1 a ha
      rw [p.property.2] at ho
      exact ho hbu
  exact Fintype.card_eq_zero

theorem actual_constrained_mate_free_multiplicity {n : ℕ}
    (C : Finset (Dart n × Dart n)) (a b : Dart n)
    (ha : a ∉ UsedDarts C) (hb : b ∉ UsedDarts C) (hab : a ≠ b) :
    (Finset.univ \ insert a (UsedDarts C)).card * ConstrainedMateCount C a b =
      PatternCount C := by
  let B := insert a (UsedDarts C)
  have hf : Finset.filter (fun c : Dart n => c ∉ B) Finset.univ =
      Finset.univ \ B := by ext c; simp
  have hs : (∑ c : Dart n, ConstrainedMateCount C a c) =
      (Finset.univ \ B).card * ConstrainedMateCount C a b := by
    calc
      (∑ c : Dart n, ConstrainedMateCount C a c) =
          ∑ c : Dart n, if c ∈ B then 0 else ConstrainedMateCount C a b := by
        apply Finset.sum_congr rfl
        intro c hc
        split_ifs with h
        · exact actual_constrained_mate_zero_forbidden C a c ha h
        · have hcu : c ∉ UsedDarts C := by
            intro hcu; exact h (Finset.mem_insert_of_mem hcu)
          have hac : a ≠ c := by
            intro hac; exact h (by subst c; exact Finset.mem_insert_self _ _)
          exact (actual_constrained_mate_distinct_constant C a b c hb hcu hab hac).symm
      _ = _ := by simp [Finset.sum_ite,hf,Finset.sum_const]
  rw [← hs]
  exact actual_constrained_mate_sum C a

theorem actual_free_dart_card {n : ℕ} (C : Finset (Dart n × Dart n))
    (a : Dart n) (ha : a ∉ UsedDarts C) :
    (Finset.univ \ insert a (UsedDarts C)).card = 3*n-(UsedDarts C).card-1 := by
  rw [Finset.card_sdiff]
  simp [Finset.card_insert_of_notMem ha,Dart,Nat.mul_comm]
  omega

theorem actual_pattern_count_recurrence {n : ℕ}
    (C : Finset (Dart n × Dart n)) (a b : Dart n)
    (ha : a ∉ UsedDarts C) (hb : b ∉ UsedDarts C) (hab : a ≠ b) :
    (3*n-(UsedDarts C).card-1) * PatternCount (insert (a,b) C) =
      PatternCount C := by
  rw [actual_pattern_insert_count]
  have h := actual_constrained_mate_free_multiplicity C a b ha hb hab
  rw [actual_free_dart_card C a ha] at h
  exact h

theorem actual_disjoint_pattern_used_card {n : ℕ}
    (C : Finset (Dart n × Dart n)) (hd : ∀ e ∈ C, e.1 ≠ e.2)
    (hdis : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) :
    (UsedDarts C).card = 2*C.card := by
  unfold UsedDarts
  rw [Finset.card_biUnion hdis]
  have hc (e : Dart n × Dart n) (he : e ∈ C) :
      ({e.1,e.2} : Finset (Dart n)).card = 2 := by
    simp [hd e he]
  calc
    (∑ e ∈ C, ({e.1,e.2} : Finset (Dart n)).card) = ∑ _e ∈ C, 2 := by
      apply Finset.sum_congr rfl
      intro e he
      exact hc e he
    _ = _ := by simp [Nat.mul_comm]

theorem actual_disjoint_pattern_count_recurrence {n : ℕ}
    (C : Finset (Dart n × Dart n)) (hd : ∀ e ∈ C, e.1 ≠ e.2)
    (hdis : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2})
    (a b : Dart n) (ha : a ∉ UsedDarts C) (hb : b ∉ UsedDarts C) (hab : a ≠ b) :
    (3*n-2*C.card-1) * PatternCount (insert (a,b) C) =
      PatternCount C := by
  have h := actual_pattern_count_recurrence C a b ha hb hab
  rw [actual_disjoint_pattern_used_card C hd hdis] at h
  exact h

#print axioms actual_constrained_mate_sum
#print axioms actual_constrained_mate_zero_forbidden
#print axioms actual_constrained_mate_free_multiplicity
#print axioms actual_free_dart_card
#print axioms actual_pattern_count_recurrence
#print axioms actual_disjoint_pattern_used_card
#print axioms actual_disjoint_pattern_count_recurrence
end Reference.MD06PairingCounts