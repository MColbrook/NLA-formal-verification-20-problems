module

public import NLA.MD06.CubicConfiguration.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CubicConfiguration
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def PairingProbability (n : ℕ) (P : Pairing n → Prop) : ℝ :=
  (Fintype.card {p : Pairing n // P p} : ℝ) / (Fintype.card (Pairing n) : ℝ)

noncomputable def SimpleConfigurationProbability (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  (Fintype.card {p : SimpleConfiguration n // P (configurationGraph p)} : ℝ) /
    (Fintype.card (SimpleConfiguration n) : ℝ)

noncomputable def ConditionedGraphProbability (n : ℕ)
    (P : SimpleGraph (Fin n) → Prop) : ℝ :=
  PairingProbability n (fun p => ∃ h : IsSimplePairing p, P (configurationGraph ⟨p,h⟩)) /
    PairingProbability n IsSimplePairing

end Reference.MD06CubicConfiguration
