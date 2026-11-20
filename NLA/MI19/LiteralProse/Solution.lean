module

public import NLA.MI19.LiteralProse.Polynomials
public import NLA.MI19.LiteralProse.Perturbation
public import NLA.MI19.LiteralProse.Inversions

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder
namespace NLA.MI19.LiteralProse.Interface

theorem full_polynomial (q : ℝ) :
    qPermanent q witness =
      115600*(q:ℂ)^6+4886140*(q:ℂ)^5+9568969*(q:ℂ)^4+4712758*(q:ℂ)^3
        -199231*(q:ℂ)^2+4886140*(q:ℂ)+4999700 := by
  exact NLA.MI19.LiteralProse.full_polynomial q

theorem restricted_polynomial (q : ℝ) :
    restrictedQPermanent q witness witnessSubset =
      4999700*(q:ℂ)^5+9482260*(q:ℂ)^4+4741130*(q:ℂ)^3+4741130*(q:ℂ)+4999700 := by
  exact NLA.MI19.LiteralProse.restricted_polynomial q

theorem factored_difference (q : ℝ) :
    qPermanent q witness-restrictedQPermanent q witness witnessSubset =
      (q:ℂ)*((q:ℂ)+1)*(115600*(q:ℂ)^4-229160*(q:ℂ)^3+315869*(q:ℂ)^2
        -344241*(q:ℂ)+145010) := by
  exact NLA.MI19.LiteralProse.factored_difference q

theorem positive_definite_perturbations :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      (witness + (ε : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)).PosDef ∧
      qPermanent witnessQ (witness + (ε : ℂ) • 1) <
        restrictedQPermanent witnessQ (witness + (ε : ℂ) • 1) witnessSubset := by
  exact NLA.MI19.LiteralProse.positive_definite_perturbations

theorem literal_inversion_example :
    inversionCount (Equiv.swap (0 : Fin 4) 2) = 3 ∧
    inversionCount (Equiv.swap (0 : Fin 3) 1) = 1 ∧
    PreservesSubset (Equiv.swap (0 : Fin 4) 2) witnessSubset ∧
    ∀ i : Fin 3, (Equiv.swap (0 : Fin 4) 2) ((1 : Fin 4).succAbove i) =
      (1 : Fin 4).succAbove ((Equiv.swap (0 : Fin 3) 1) i) := by
  exact NLA.MI19.LiteralProse.literal_inversion_example

end NLA.MI19.LiteralProse.Interface
