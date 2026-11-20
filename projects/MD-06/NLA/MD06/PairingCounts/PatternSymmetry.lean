module

public import NLA.MD06.PairingCounts.PatternDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06PairingCounts
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_pattern_endpoints_used {n : ℕ} (C : Finset (Dart n × Dart n))
    (e : Dart n × Dart n) (he : e ∈ C) :
    e.1 ∈ UsedDarts C ∧ e.2 ∈ UsedDarts C := by
  constructor
  · exact Finset.mem_biUnion.mpr ⟨e,he,by simp⟩
  · exact Finset.mem_biUnion.mpr ⟨e,he,by simp⟩

theorem actual_matching_partner_outside {n : ℕ} (C : Finset (Dart n × Dart n))
    (p : Pairing n) (hp : Matches C p) (a : Dart n) (ha : a ∉ UsedDarts C) :
    p.val a ∉ UsedDarts C := by
  intro h
  obtain ⟨e,he,hmem⟩ := Finset.mem_biUnion.mp h
  simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
  have hu := actual_pattern_endpoints_used C e he
  have hpe := hp e he
  rcases hmem with h1 | h2
  · have haa : a = e.2 := by
      calc a = p.val (p.val a) := (p.property.1 a).symm
           _ = p.val e.1 := congrArg p.val h1
           _ = e.2 := hpe
    exact ha (haa.symm ▸ hu.2)
  · have haa : a = e.1 := by
      calc a = p.val (p.val a) := (p.property.1 a).symm
           _ = p.val e.2 := congrArg p.val h2
           _ = e.1 := by rw [← hpe]; exact p.property.1 e.1
    exact ha (haa.symm ▸ hu.1)

theorem actual_relabel_matches_fixed_support {n : ℕ}
    (C : Finset (Dart n × Dart n)) (τ : Equiv.Perm (Dart n))
    (hτ : ∀ x ∈ UsedDarts C, τ x = x) (p : Pairing n) :
    Matches C (relabelPairing τ p) ↔ Matches C p := by
  constructor
  · intro h e he
    have hu := actual_pattern_endpoints_used C e he
    have h1 := hτ e.1 hu.1
    have h2 := hτ e.2 hu.2
    have hi : τ.symm e.1 = e.1 := τ.symm_apply_eq.mpr h1.symm
    have hx := h e he
    change τ (p.val (τ.symm e.1)) = e.2 at hx
    rw [hi] at hx
    exact τ.injective (hx.trans h2.symm)
  · intro h e he
    have hu := actual_pattern_endpoints_used C e he
    have h1 := hτ e.1 hu.1
    have h2 := hτ e.2 hu.2
    have hi : τ.symm e.1 = e.1 := τ.symm_apply_eq.mpr h1.symm
    change τ (p.val (τ.symm e.1)) = e.2
    rw [hi,h e he,h2]

theorem actual_constrained_mate_distinct_constant {n : ℕ}
    (C : Finset (Dart n × Dart n)) (a b c : Dart n)
    (hb : b ∉ UsedDarts C) (hc : c ∉ UsedDarts C)
    (hab : a ≠ b) (hac : a ≠ c) :
    ConstrainedMateCount C a b = ConstrainedMateCount C a c := by
  let τ : Equiv.Perm (Dart n) := Equiv.swap b c
  have hτ : ∀ x ∈ UsedDarts C, τ x = x := by
    intro x hx
    have hxb : x ≠ b := by intro h; subst x; exact hb hx
    have hxc : x ≠ c := by intro h; subst x; exact hc hx
    exact Equiv.swap_apply_of_ne_of_ne hxb hxc
  have ha : τ a = a := Equiv.swap_apply_of_ne_of_ne hab hac
  have ht : τ b = c := Equiv.swap_apply_left b c
  unfold ConstrainedMateCount
  exact Fintype.card_congr
    (Equiv.subtypeEquiv (pairingRelabelEquiv τ) (by
      intro p
      change (Matches C p ∧ p.val a = b) ↔
        (Matches C (relabelPairing τ p) ∧ (relabelPairing τ p).val a = c)
      rw [actual_relabel_matches_fixed_support C τ hτ p]
      have hi : τ.symm a = a := τ.symm_apply_eq.mpr ha.symm
      change (Matches C p ∧ p.val a = b) ↔ (Matches C p ∧ τ (p.val (τ.symm a)) = c)
      rw [hi,← ht]
      simp))

theorem actual_pattern_insert_count {n : ℕ} (C : Finset (Dart n × Dart n))
    (a b : Dart n) :
    PatternCount (insert (a,b) C) = ConstrainedMateCount C a b := by
  unfold PatternCount ConstrainedMateCount
  exact Fintype.card_congr (Equiv.subtypeEquivRight (by
    intro p
    simp [Matches,and_comm]))

#print axioms actual_pattern_endpoints_used
#print axioms actual_matching_partner_outside
#print axioms actual_relabel_matches_fixed_support
#print axioms actual_constrained_mate_distinct_constant
#print axioms actual_pattern_insert_count
end Reference.MD06PairingCounts