module

public import NLA.MD06.CyclePairPatterns.Definitions
public import NLA.MD06.PairingCounts.PatternProbability

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CyclePairPatterns
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06PairingCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_outgoing_injective {n ell : ℕ} (D : CycleData n ell) :
    Function.Injective (outgoing D) := by
  intro i j h
  exact D.1.injective (congrArg Prod.fst h)

theorem actual_incoming_injective {n ell : ℕ} (D : CycleData n ell) :
    Function.Injective (incoming D) := by
  intro i j h
  exact D.1.injective (congrArg Prod.fst h)

theorem actual_outgoing_ne_incoming {n ell : ℕ} (D : CycleData n ell)
    (i j : Fin ell) : outgoing D i ≠ incoming D j := by
  intro h
  have hij := D.1.injective (congrArg Prod.fst h)
  subst j
  have hlabel := congrArg Prod.snd h
  exact (D.2 i).property hlabel.symm

theorem actual_cycle_edge_injective {n ell : ℕ} (D : CycleData n ell) :
    Function.Injective (cycleEdge D) := by
  intro i j h
  exact actual_outgoing_injective D (congrArg Prod.fst h)

theorem actual_cycle_pattern_card {n ell : ℕ} (D : CycleData n ell) :
    (CyclePattern D).card = ell := by
  unfold CyclePattern
  rw [Finset.card_image_of_injective _ (actual_cycle_edge_injective D)]
  simp

theorem actual_cycle_pattern_distinct_endpoints {n ell : ℕ} (D : CycleData n ell) :
    ∀ e ∈ CyclePattern D, e.1 ≠ e.2 := by
  intro e he
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
  exact actual_outgoing_ne_incoming D i (finRotate ell i)

theorem actual_cycle_pattern_disjoint_endpoints {n ell : ℕ} (D : CycleData n ell) :
    ∀ e ∈ CyclePattern D, ∀ f ∈ CyclePattern D, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  intro e he f hf hef
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hf
  have hij : i ≠ j := by intro h; subst j; exact hef rfl
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hij (actual_outgoing_injective D (hx.symm.trans hy))
  · exact actual_outgoing_ne_incoming D i (finRotate ell j) (hx.symm.trans hy)
  · exact actual_outgoing_ne_incoming D j (finRotate ell i) (hy.symm.trans hx)
  · exact hij ((finRotate ell).injective
      (actual_incoming_injective D (hx.symm.trans hy)))

theorem actual_cycle_matching_graph_adjacency {n ell : ℕ} (D : CycleData n ell)
    (p : SimpleConfiguration n) (hp : Matches (CyclePattern D) p.val) (i : Fin ell) :
    (configurationGraph p).Adj (D.1 i) (D.1 (finRotate ell i)) := by
  refine ⟨(D.2 i).val.2,?_⟩
  have h := hp (cycleEdge D i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  exact congrArg Prod.fst h

theorem actual_uniform_pairing_cycle_pattern_probability (k ell : ℕ)
    (D : CycleData (Size k) ell) :
    ((UniformPairing k).toOuterMeasure {p | Matches (CyclePattern D) p}).toReal =
      1 / (PairingDenominator (Size k) ell : ℝ) := by
  have h := actual_uniform_pairing_disjoint_pattern_probability k (CyclePattern D)
    (actual_cycle_pattern_distinct_endpoints D) (actual_cycle_pattern_disjoint_endpoints D)
  rw [actual_cycle_pattern_card D] at h
  exact h

#print axioms actual_outgoing_injective
#print axioms actual_incoming_injective
#print axioms actual_outgoing_ne_incoming
#print axioms actual_cycle_edge_injective
#print axioms actual_cycle_pattern_card
#print axioms actual_cycle_pattern_distinct_endpoints
#print axioms actual_cycle_pattern_disjoint_endpoints
#print axioms actual_cycle_matching_graph_adjacency
#print axioms actual_uniform_pairing_cycle_pattern_probability
end Reference.MD06CyclePairPatterns