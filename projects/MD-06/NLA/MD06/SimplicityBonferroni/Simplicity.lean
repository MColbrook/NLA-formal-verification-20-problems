module

public import NLA.MD06.SimplicityBonferroni.Bonferroni

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Simplicity
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_matching_loop_exists {n : ℕ} (p : Pairing n)
    (u : Fin n) (a : Fin 3) (h : (p.val (u,a)).fst = u) :
    ∃ d : LoopDatum n, Matches (LoopPattern d) p := by
  let b := (p.val (u,a)).snd
  have heq : p.val (u,a) = (u,b) := Prod.ext h rfl
  have hab : a ≠ b := by
    intro hab
    exact p.property.2 (u,a) (heq.trans (by rw [hab]))
  rcases lt_or_gt_of_ne hab with hab | hba
  · refine ⟨⟨u,⟨(a,b),hab⟩⟩,?_⟩
    simpa [Matches,LoopPattern] using heq
  · have hinv : p.val (u,b) = (u,a) := by
      rw [← heq]
      exact p.property.1 (u,a)
    refine ⟨⟨u,⟨(b,a),hba⟩⟩,?_⟩
    simpa [Matches,LoopPattern] using hinv

theorem actual_matching_double_sorted_exists {n : ℕ} (p : Pairing n)
    (u v : Fin n) (huv : u < v) (a b c d : Fin 3)
    (hab : a ≠ b) (hcd : c ≠ d)
    (h1 : p.val (u,a) = (v,c)) (h2 : p.val (u,b) = (v,d)) :
    ∃ z : DoubleDatum n, Matches (DoublePattern z) p := by
  rcases lt_or_gt_of_ne hab with hab | hba <;>
    rcases lt_or_gt_of_ne hcd with hcd | hdc
  · refine ⟨⟨⟨(u,v),huv⟩,⟨(a,b),hab⟩,⟨(c,d),hcd⟩,false⟩,?_⟩
    simp [Matches,DoublePattern,h1,h2]
  · refine ⟨⟨⟨(u,v),huv⟩,⟨(a,b),hab⟩,⟨(d,c),hdc⟩,true⟩,?_⟩
    simp [Matches,DoublePattern,h1,h2]
  · refine ⟨⟨⟨(u,v),huv⟩,⟨(b,a),hba⟩,⟨(c,d),hcd⟩,true⟩,?_⟩
    simp [Matches,DoublePattern,h1,h2]
  · refine ⟨⟨⟨(u,v),huv⟩,⟨(b,a),hba⟩,⟨(d,c),hdc⟩,false⟩,?_⟩
    simp [Matches,DoublePattern,h1,h2]

theorem actual_matching_double_exists {n : ℕ} (p : Pairing n)
    (u v : Fin n) (huv : u ≠ v) (a b c d : Fin 3)
    (hab : a ≠ b) (hcd : c ≠ d)
    (h1 : p.val (u,a) = (v,c)) (h2 : p.val (u,b) = (v,d)) :
    ∃ z : DoubleDatum n, Matches (DoublePattern z) p := by
  rcases lt_or_gt_of_ne huv with huv | hvu
  · exact actual_matching_double_sorted_exists p u v huv a b c d hab hcd h1 h2
  · have hi1 : p.val (v,c) = (u,a) := by
      rw [← h1]
      exact p.property.1 (u,a)
    have hi2 : p.val (v,d) = (u,b) := by
      rw [← h2]
      exact p.property.1 (u,b)
    exact actual_matching_double_sorted_exists p v u hvu c d a b hcd hab hi1 hi2

theorem actual_simple_pairing_iff_no_bad_pattern {n : ℕ} (p : Pairing n) :
    IsSimplePairing p ↔ ∀ z : BadDatum n, ¬ Matches (BadPattern z) p := by
  constructor
  · intro hs z hz
    rcases z with z | z
    · have h := hz ((z.1,z.2.val.1),(z.1,z.2.val.2)) (by simp [BadPattern,LoopPattern])
      exact hs.1 z.1 z.2.val.1 (congrArg Prod.fst h)
    · let u := z.1.val.1
      let v := z.1.val.2
      let a := z.2.1.val.1
      let b := z.2.1.val.2
      have hab : a ≠ b := ne_of_lt z.2.1.property
      have htarget : (p.val (u,a)).fst = (p.val (u,b)).fst := by
        cases hb : z.2.2.2 with
        | false =>
          have h1 := hz ((u,a),(v,z.2.2.1.val.1)) (by simp [BadPattern,DoublePattern,hb,u,a,v])
          have h2 := hz ((u,b),(v,z.2.2.1.val.2)) (by simp [BadPattern,DoublePattern,hb,u,b,v])
          exact (congrArg Prod.fst h1).trans (congrArg Prod.fst h2).symm
        | true =>
          have h1 := hz ((u,a),(v,z.2.2.1.val.2)) (by simp [BadPattern,DoublePattern,hb,u,a,v])
          have h2 := hz ((u,b),(v,z.2.2.1.val.1)) (by simp [BadPattern,DoublePattern,hb,u,b,v])
          exact (congrArg Prod.fst h1).trans (congrArg Prod.fst h2).symm
      exact hab (hs.2 u htarget)
  · intro h
    have hlo : ∀ u : Fin n, ∀ a : Fin 3, (p.val (u,a)).fst ≠ u := by
      intro u a heq
      obtain ⟨z,hz⟩ := actual_matching_loop_exists p u a heq
      exact h (.inl z) hz
    refine ⟨hlo,?_⟩
    intro u a b heq
    by_contra hab
    let v := (p.val (u,a)).fst
    let c := (p.val (u,a)).snd
    let d := (p.val (u,b)).snd
    have h1 : p.val (u,a) = (v,c) := rfl
    have h2 : p.val (u,b) = (v,d) := Prod.ext heq.symm rfl
    have hcd : c ≠ d := by
      intro hcd
      have hs : p.val (u,a) = p.val (u,b) := h1.trans (by rw [hcd]; exact h2.symm)
      exact hab (congrArg Prod.snd (p.val.injective hs))
    have huv : u ≠ v := (hlo u a).symm
    obtain ⟨z,hz⟩ := actual_matching_double_exists p u v huv a b c d hab hcd h1 h2
    exact h (.inr z) hz

theorem actual_simple_pairing_iff_bad_count_zero {n : ℕ} (p : Pairing n) :
    IsSimplePairing p ↔ BadCount p = 0 := by
  rw [actual_simple_pairing_iff_no_bad_pattern]
  constructor
  · intro h
    have : IsEmpty {z : BadDatum n // Matches (BadPattern z) p} :=
      ⟨fun z => h z.val z.property⟩
    simp [BadCount]
  · intro h z hz
    have : Nonempty {z : BadDatum n // Matches (BadPattern z) p} := ⟨⟨z,hz⟩⟩
    exact Fintype.card_ne_zero h

theorem actual_simple_indicator_bonferroni_seven {n : ℕ} (p : Pairing n) :
    (∑ i ∈ Finset.range 8, (-1 : ℝ)^i * ((BadCount p).choose i : ℝ)) ≤
      if IsSimplePairing p then (1 : ℝ) else 0 := by
  have h := actual_pairing_bad_bonferroni_seven p
  simpa only [← actual_simple_pairing_iff_bad_count_zero p] using h

#print axioms actual_simple_indicator_bonferroni_seven
#print axioms actual_matching_loop_exists
#print axioms actual_matching_double_sorted_exists
#print axioms actual_matching_double_exists
#print axioms actual_simple_pairing_iff_no_bad_pattern
#print axioms actual_simple_pairing_iff_bad_count_zero
end Reference.MD06Simplicity