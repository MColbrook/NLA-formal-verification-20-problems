module

public import NLA.MD06.PairingCounts.PatternRecurrence
public import NLA.MD06.PairingCounts.ProductDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06PairingCounts
open Reference.MD06CubicConfiguration
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_pairing_denominator_zero (n : ℕ) : PairingDenominator n 0 = 1 := by
  simp [PairingDenominator]

theorem actual_pairing_denominator_succ (n t : ℕ) :
    PairingDenominator n (t+1) = PairingDenominator n t * (3*n-2*t-1) := by
  exact Finset.prod_range_succ _ t

theorem actual_disjoint_pattern_count_product {n : ℕ}
    (C : Finset (Dart n × Dart n)) (hd : ∀ e ∈ C, e.1 ≠ e.2)
    (hdis : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) :
    PatternCount C * PairingDenominator n C.card = Fintype.card (Pairing n) := by
  revert hd hdis
  induction C using Finset.induction_on with
  | empty =>
    intro hd hdis
    simp [PatternCount,Matches,PairingDenominator]
  | @insert e C he ih =>
    rcases e with ⟨a,b⟩
    intro hd hdis
    have hdC : ∀ f ∈ C, f.1 ≠ f.2 := by
      intro f hf
      exact hd f (Finset.mem_insert_of_mem hf)
    have hdisC : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
        Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
      intro e he f hf hef
      exact hdis e (Finset.mem_insert_of_mem he) f (Finset.mem_insert_of_mem hf) hef
    have hab : a ≠ b := hd (a,b) (Finset.mem_insert_self _ _)
    have ha : a ∉ UsedDarts C := by
      intro hx
      obtain ⟨f,hf,hmem⟩ := Finset.mem_biUnion.mp hx
      have hef : (a,b) ≠ f := by intro h; subst f; exact he hf
      have hh := hdis (a,b) (Finset.mem_insert_self _ _) f
        (Finset.mem_insert_of_mem hf) hef
      exact Finset.disjoint_left.mp hh (by simp) hmem
    have hb : b ∉ UsedDarts C := by
      intro hx
      obtain ⟨f,hf,hmem⟩ := Finset.mem_biUnion.mp hx
      have hef : (a,b) ≠ f := by intro h; subst f; exact he hf
      have hh := hdis (a,b) (Finset.mem_insert_self _ _) f
        (Finset.mem_insert_of_mem hf) hef
      exact Finset.disjoint_left.mp hh (by simp) hmem
    have hr := actual_disjoint_pattern_count_recurrence C hdC hdisC a b ha hb hab
    rw [Finset.card_insert_of_notMem he,actual_pairing_denominator_succ]
    calc
      PatternCount (insert (a,b) C) *
          (PairingDenominator n C.card * (3*n-2*C.card-1)) =
        ((3*n-2*C.card-1) * PatternCount (insert (a,b) C)) *
          PairingDenominator n C.card := by ring
      _ = PatternCount C * PairingDenominator n C.card := by rw [hr]
      _ = Fintype.card (Pairing n) := ih hdC hdisC

#print axioms actual_pairing_denominator_zero
#print axioms actual_pairing_denominator_succ
#print axioms actual_disjoint_pattern_count_product
end Reference.MD06PairingCounts