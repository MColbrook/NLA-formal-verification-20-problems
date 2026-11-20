module

public import NLA.IV04.PaperFractionCoefficientBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem fraction_coefficient_state_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionCoefficientState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => fractionCoefficientInitial (v 0)
  let step : (Fin 2 → List Bool) → List Bool := fun v => fractionCoefficientStep (v 0)
  let two : (Fin 2 → List Bool) → List Bool := fun v => v 1 ++ v 1
  let four : (Fin 2 → List Bool) → List Bool := fun v => two v ++ two v
  let eight : (Fin 2 → List Bool) → List Bool := fun v => four v ++ four v
  let sixteen : (Fin 2 → List Bool) → List Bool := fun v => eight v ++ eight v
  let scale : (Fin 2 → List Bool) → List Bool := fun v => sixteen v ++ sixteen v ++ List.replicate 64 false
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    smash (v 0) (scale v) ++ v 1 ++ v 1 ++ List.replicate 6 false
  have hi : Cobham initial := fraction_coefficient_initial_cobham
  have hs : Cobham step :=
    (Cobham.comp fraction_coefficient_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have htwo : Cobham two := Cobham.appendFn (.proj 1) (.proj 1)
  have hfour : Cobham four := Cobham.appendFn htwo htwo
  have height : Cobham eight := Cobham.appendFn hfour hfour
  have hsixteen : Cobham sixteen := Cobham.appendFn height height
  have hscale : Cobham scale :=
    Cobham.appendFn (Cobham.appendFn hsixteen hsixteen) (.const (List.replicate 64 false))
  have hproduct := Cobham.comp₂ Cobham.smash (Cobham.proj (0 : Fin 2)) hscale
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn hproduct (.proj 1)) (.proj 1)) (.const (List.replicate 6 false))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((fractionCoefficientStep^[clock.length]) (fractionCoefficientInitial (v 0))).length ≤ _
    have h := fraction_coefficient_initial_iterate_length clock.length (v 0)
    have hm := Nat.mul_le_mul_left clock.length
      (show 18*(v 0).length+36 ≤ 32*(v 0).length+64 by omega)
    simp [ruler,scale,sixteen,eight,four,two]
    nlinarith [h,hm]
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit hargs).of_eq fun _ => rfl

theorem polynomial_fraction_coefficients_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialFractionCoefficients (v 0) :=
  (Cobham.sndBlockFn (Cobham.sndBlockFn fraction_coefficient_state_cobham)).of_eq fun _ => rfl

theorem polynomial_fraction_coefficients_mem_fp : polynomialFractionCoefficients ∈ FP :=
  CobhamFP_subset_FP polynomial_fraction_coefficients_cobham

set_option maxHeartbeats 2000000 in
theorem encoded_rational_list_clearing_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedRationalListClearing (v 0) := by
  have h := encoded_rational_list_parser_cobham
  have hfractions := Cobham.fstBlockFn (Cobham.sndBlockFn h)
  have hcoefs := Cobham.comp polynomial_fraction_coefficients_cobham fun _ : Fin 1 => hfractions
  have htail := Cobham.sndBlockFn (Cobham.sndBlockFn h)
  exact (Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn h)
    (Cobham.comp₂ Cobham.pairing rational_list_denominator_cobham
      (Cobham.comp₂ Cobham.pairing hcoefs htail))).of_eq fun _ => rfl

theorem encoded_rational_list_clearing_mem_fp : encodedRationalListClearing ∈ FP :=
  CobhamFP_subset_FP encoded_rational_list_clearing_cobham

#print axioms encoded_rational_list_clearing_mem_fp
end IV04.Paper.Computational
