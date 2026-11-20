module

public import NLA.MD06.CubicConfiguration.UniformDefinitions
public import NLA.MD06.CubicConfiguration.Fibers
public import NLA.MD06.CubicConfiguration.FiniteFibers
public import NLA.MD06.FiniteProbability.FiniteBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CubicConfiguration
open Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def configurationCubic (k : ℕ) (p : SimpleConfiguration (Size k)) :
    CubicSample k := ⟨configurationGraph p,actual_configuration_graph_cubic p⟩

theorem actual_configuration_cubic_fiber_card (k : ℕ) (g : CubicSample k) :
    Fintype.card {p : SimpleConfiguration (Size k) // configurationCubic k p = g} =
      6^(Size k) := by
  let e : {p : SimpleConfiguration (Size k) // configurationCubic k p = g} ≃
      {p : SimpleConfiguration (Size k) // configurationGraph p = g.val} :=
    Equiv.subtypeEquivRight (by
      intro p
      constructor
      · intro h; exact congrArg Subtype.val h
      · intro h; exact Subtype.ext h)
  rw [Fintype.card_congr e]
  exact actual_simple_cubic_configuration_fiber_card g.val g.property

theorem actual_simple_configuration_nonempty (k : ℕ) :
    Nonempty (SimpleConfiguration (Size k)) := by
  obtain ⟨g⟩ := actual_cubic_sample_nonempty k
  obtain ⟨f⟩ := actual_neighbor_frames_nonempty g.val g.property
  exact ⟨framesConfiguration f⟩

theorem actual_pairing_nonempty (k : ℕ) : Nonempty (Pairing (Size k)) := by
  obtain ⟨p⟩ := actual_simple_configuration_nonempty k
  exact ⟨p.val⟩

theorem actual_simple_configuration_total_card (k : ℕ) :
    Fintype.card (SimpleConfiguration (Size k)) =
      Fintype.card (CubicSample k) * 6^(Size k) :=
  actual_constant_fiber_total (configurationCubic k) (6^(Size k))
    (by intro g; simpa only [← Nat.card_eq_fintype_card] using actual_configuration_cubic_fiber_card k g)

theorem actual_simple_configuration_uniform_graph_law (k : ℕ)
    (P : SimpleGraph (Fin (Size k)) → Prop) :
    SimpleConfigurationProbability (Size k) P = GraphProbability k P := by
  change countingProbability (fun p : SimpleConfiguration (Size k) =>
    P (configurationGraph p)) = _
  rw [actual_graph_probability_sample_formula]
  exact actual_constant_fiber_probability (configurationCubic k) (6^(Size k))
    (by intro g; simpa only [← Nat.card_eq_fintype_card] using actual_configuration_cubic_fiber_card k g) (by positivity)
    (fun g : CubicSample k => P g.val)

theorem actual_simple_pairing_graph_event_card {n : ℕ}
    (P : SimpleGraph (Fin n) → Prop) :
    Fintype.card {p : Pairing n // ∃ h : IsSimplePairing p, P (configurationGraph ⟨p,h⟩)} =
      Fintype.card {p : SimpleConfiguration n // P (configurationGraph p)} := by
  let e : {p : Pairing n // ∃ h : IsSimplePairing p, P (configurationGraph ⟨p,h⟩)} ≃
      {p : SimpleConfiguration n // P (configurationGraph p)} :=
    { toFun := fun p => ⟨⟨p.val,Classical.choose p.property⟩,Classical.choose_spec p.property⟩
      invFun := fun p => ⟨p.val.val,⟨p.val.property,p.property⟩⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro p; apply Subtype.ext; apply Subtype.ext; rfl }
  exact Fintype.card_congr e

theorem actual_pairing_simple_conditioning (k : ℕ)
    (P : SimpleGraph (Fin (Size k)) → Prop) :
    ConditionedGraphProbability (Size k) P =
      SimpleConfigurationProbability (Size k) P := by
  have : Nonempty (Pairing (Size k)) := actual_pairing_nonempty k
  have : Nonempty (SimpleConfiguration (Size k)) := actual_simple_configuration_nonempty k
  have hn : (Fintype.card (Pairing (Size k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hs : (Fintype.card (SimpleConfiguration (Size k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold ConditionedGraphProbability PairingProbability SimpleConfigurationProbability
  have he := actual_simple_pairing_graph_event_card P
  simp only [← Nat.card_eq_fintype_card] at he hn hs ⊢
  rw [he]
  field_simp

theorem actual_configuration_conditioned_uniform_graph_law (k : ℕ)
    (P : SimpleGraph (Fin (Size k)) → Prop) :
    ConditionedGraphProbability (Size k) P = GraphProbability k P :=
  (actual_pairing_simple_conditioning k P).trans
    (actual_simple_configuration_uniform_graph_law k P)

#print axioms actual_configuration_cubic_fiber_card
#print axioms actual_simple_configuration_nonempty
#print axioms actual_pairing_nonempty
#print axioms actual_simple_configuration_total_card
#print axioms actual_simple_configuration_uniform_graph_law
#print axioms actual_simple_pairing_graph_event_card
#print axioms actual_pairing_simple_conditioning
#print axioms actual_configuration_conditioned_uniform_graph_law
end Reference.MD06CubicConfiguration
