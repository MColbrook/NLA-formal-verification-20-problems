module

public import NLA.IV04.PaperBudgetedPowerBounds
public import NLA.IV04.PaperMatrixCoefficientInputPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem budgeted_power_step_cobham :
    Cobham fun v : Fin 1 → List Bool => budgetedPowerStep (v 0) := by
  have hc := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hb := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hp := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hd := unary_input_cobham_comp decrement_count_cobham hc
  have hm : Cobham fun v : Fin 1 → List Bool =>
      canonicalWordMultiply (pairSnd (pairSnd (v 0))) (pairFst (pairSnd (v 0))) :=
    (Cobham.comp₂ canonical_word_multiply_cobham hp hb).of_eq fun _ => rfl
  have hn := input_pair_cobham_comp hd (input_pair_cobham_comp hb hm)
  exact (Cobham.iteFn (Cobham.nonemptyFn hc) hn (.proj 0)).of_eq fun _ => rfl

theorem budgeted_power_state_cobham :
    Cobham fun v : Fin 1 → List Bool => budgetedPowerState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v =>
    pair (canonicalWord (pairFst (v 0))) (pair (pairFst (pairSnd (v 0))) [true])
  let step : (Fin 2 → List Bool) → List Bool := fun v => budgetedPowerStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ v 1 ++ v 1 ++ List.replicate 5 false ++ smash (v 0) (v 1)
  have hi : Cobham initial := input_pair_cobham_comp
    (unary_input_cobham_comp canonical_word_cobham (Cobham.fstBlockFn (.proj 0)))
    (input_pair_cobham_comp (Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0))) (.const [true]))
  have hs : Cobham step :=
    (Cobham.comp budgeted_power_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1))
      (.proj 1)) (.proj 1)) (.const (List.replicate 5 false)))
    ((Cobham.comp₂ Cobham.smash (.proj 0) (.proj 1)).of_eq fun _ => rfl)
  have hbound : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((budgetedPowerStep^[clock.length])
      (pair (canonicalWord (pairFst (v 0))) (pair (pairFst (pairSnd (v 0))) [true]))).length ≤ _
    have h := budgeted_power_clock_length clock (v 0)
    simp [ruler,smash_length]
    omega
  have hit := Cobham.iterFn hi hs hr hbound
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit hargs).of_eq fun _ => rfl

theorem polynomial_budgeted_power_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialBudgetedPower (v 0) :=
  (Cobham.sndBlockFn (Cobham.sndBlockFn budgeted_power_state_cobham)).of_eq fun _ => rfl

theorem polynomial_budgeted_power_mem_fp : polynomialBudgetedPower ∈ FP :=
  CobhamFP_subset_FP polynomial_budgeted_power_cobham

theorem matrix_denominator_power_argument_cobham :
    Cobham fun v : Fin 1 → List Bool => matrixDenominatorPowerArgument (v 0) := by
  have hd := Cobham.fstBlockFn (Cobham.sndBlockFn encoded_matrix_coefficient_input_cobham)
  have hD := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn encoded_matrix_coefficient_input_cobham))
  simpa only [matrixDenominatorPowerArgument] using
    input_pair_cobham_comp hd (input_pair_cobham_comp hD (Cobham.proj (0 : Fin 1)))

theorem encoded_matrix_denominator_power_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedMatrixDenominatorPower (v 0) := by
  simpa only [encodedMatrixDenominatorPower] using
    unary_input_cobham_comp polynomial_budgeted_power_cobham matrix_denominator_power_argument_cobham

theorem encoded_matrix_denominator_power_mem_fp : encodedMatrixDenominatorPower ∈ FP :=
  CobhamFP_subset_FP encoded_matrix_denominator_power_cobham

#print axioms polynomial_budgeted_power_mem_fp
#print axioms encoded_matrix_denominator_power_mem_fp
end IV04.Paper.Computational
