module

public import NLA.MD06.CubicConfiguration.CanonicalPairing
public import NLA.MD06.CubicConfiguration.UniformLaw

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CubicConfiguration
open Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

theorem actual_uniform_pairing_event_mass (k : ℕ) (P : Pairing (Size k) → Prop) :
    (UniformPairing k).toOuterMeasure {p | P p} =
      (Fintype.card {p : Pairing (Size k) // P p} : ENNReal) /
        Fintype.card (Pairing (Size k)) :=by
  classical
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  simp only [Set.indicator_apply, UniformPairing, PMF.ofFintype_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype, div_eq_mul_inv, Set.mem_setOf_eq]

theorem actual_pairing_probability_uniform_real (k : ℕ)
    (P : Pairing (Size k) → Prop) :
    ((UniformPairing k).toOuterMeasure {p | P p}).toReal =
      PairingProbability (Size k) P := by
  rw [actual_uniform_pairing_event_mass]
  simp [ENNReal.toReal_div,PairingProbability]

theorem actual_uniform_pairing_simple_probability_positive (k : ℕ) :
    0 < ((UniformPairing k).toOuterMeasure {p | IsSimplePairing p}).toReal := by
  rw [actual_pairing_probability_uniform_real]
  have : Nonempty (SimpleConfiguration (Size k)) :=
    actual_simple_configuration_nonempty k
  have hs : 0 < Fintype.card (SimpleConfiguration (Size k)) :=
    Fintype.card_pos
  have hn : 0 < Fintype.card (Pairing (Size k)) := Fintype.card_pos
  unfold PairingProbability
  simp only [← Nat.card_eq_fintype_card] at hs hn ⊢
  exact div_pos (by exact_mod_cast hs) (by exact_mod_cast hn)

theorem actual_uniform_pairing_conditioned_uniform_graph_law (k : ℕ)
    (P : SimpleGraph (Fin (Size k)) → Prop) :
    ((UniformPairing k).toOuterMeasure
      {p | ∃ h : IsSimplePairing p, P (configurationGraph ⟨p,h⟩)}).toReal /
      ((UniformPairing k).toOuterMeasure {p | IsSimplePairing p}).toReal =
        GraphProbability k P := by
  rw [actual_pairing_probability_uniform_real,
    actual_pairing_probability_uniform_real]
  exact actual_configuration_conditioned_uniform_graph_law k P

#print axioms actual_uniform_pairing_event_mass
#print axioms actual_pairing_probability_uniform_real
#print axioms actual_uniform_pairing_simple_probability_positive
#print axioms actual_uniform_pairing_conditioned_uniform_graph_law
end Reference.MD06CubicConfiguration