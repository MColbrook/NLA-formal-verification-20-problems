module

public import NLA.IV04.PaperFractionListDenominatorsBounds
public import NLA.IV04.PaperWordListProductPoly
public import NLA.IV04.PaperRationalListMachinePoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem fraction_list_denominators_step_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionListDenominatorsStep (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have ho := Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))
  have hd := Cobham.sndBlockFn (Cobham.fstBlockFn hr)
  have hout := Cobham.comp₂ Cobham.pairing hd ho
  have hn := Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hr) hout
  exact (Cobham.iteFn (Cobham.nonemptyFn hr) hn (Cobham.proj 0)).of_eq fun _ => rfl

theorem fraction_list_denominators_state_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionListDenominatorsState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => pair (v 0) []
  let step : (Fin 2 → List Bool) → List Bool := fun v => fractionListDenominatorsStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 0 ++ v 0 ++ v 1 ++ v 1 ++ List.replicate 2 false
  have hi : Cobham initial := Cobham.comp₂ Cobham.pairing (.proj 0) (.const [])
  have hs : Cobham step :=
    (Cobham.comp fraction_list_denominators_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 0)) (.proj 1)) (.proj 1))
    (.const (List.replicate 2 false))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((fractionListDenominatorsStep^[clock.length]) (pair (v 0) [])).length ≤ _
    have h := fraction_list_denominators_iterate_length clock.length (v 0) []
    simp only [List.length_nil] at h
    simp [ruler]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit hargs).of_eq fun _ => rfl

theorem polynomial_fraction_list_denominators_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialFractionListDenominators (v 0) :=
  (Cobham.sndBlockFn fraction_list_denominators_state_cobham).of_eq fun _ => rfl

theorem polynomial_fraction_list_denominators_mem_fp : polynomialFractionListDenominators ∈ FP :=
  CobhamFP_subset_FP polynomial_fraction_list_denominators_cobham

theorem rational_list_denominator_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialRationalListDenominator (v 0) := by
  have ho := Cobham.fstBlockFn (Cobham.sndBlockFn encoded_rational_list_parser_cobham)
  have hd := Cobham.comp polynomial_fraction_list_denominators_cobham fun _ : Fin 1 => ho
  have hp : Cobham fun v : Fin 1 → List Bool => polynomialWordListProduct (v 0) :=
    (Cobham.sndBlockFn word_list_product_state_cobham).of_eq fun _ => rfl
  have hprod := Cobham.comp hp fun _ : Fin 1 => hd
  exact (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hprod).of_eq fun _ => rfl

theorem rational_list_denominator_mem_fp : polynomialRationalListDenominator ∈ FP :=
  CobhamFP_subset_FP rational_list_denominator_cobham

#print axioms rational_list_denominator_mem_fp
end IV04.Paper.Computational
