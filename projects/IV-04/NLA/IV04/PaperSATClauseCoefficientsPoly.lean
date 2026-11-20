module

public import NLA.IV04.PaperSATClauseCoefficientsBounds
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational
 theorem clause_coefficient_pack_cobham {n : ℕ}
    {rest query output : (Fin n → List Bool) → List Bool}
    (hr : Cobham rest) (hq : Cobham query) (ho : Cobham output) :
    Cobham fun v => clauseCoefficientPack (rest v) (query v) (output v) :=
  (Cobham.comp₂ Cobham.pairing hr (Cobham.comp₂ Cobham.pairing hq ho)).of_eq fun _ => rfl
 theorem clause_coefficient_step_cobham :
    Cobham fun v : Fin 1 → List Bool => clauseCoefficientStep (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hq := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have ho := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hc := Cobham.comp polynomial_literal_match_count_cobham fun _ : Fin 1 =>
    Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn hr) hq
  exact (Cobham.iteFn (Cobham.nonemptyFn hr)
    (clause_coefficient_pack_cobham (Cobham.sndBlockFn hr) hq
      (Cobham.comp₂ Cobham.pairing hc ho)) (.proj 0)).of_eq fun _ => rfl
 theorem clause_coefficient_state_cobham :
    Cobham fun v : Fin 1 → List Bool => clauseCoefficientState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v =>
    clauseCoefficientPack (pairFst (v 0)) (pairSnd (v 0)) []
  let step : (Fin 2 → List Bool) → List Bool := fun v => clauseCoefficientStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    Complexity.smash (v 1) (List.replicate 24 false) ++ List.replicate 4 false ++
      Complexity.smash (v 0)
        (Complexity.smash (v 1) (List.replicate 12 false) ++ List.replicate 34 false)
  have hi : Cobham initial := clause_coefficient_pack_cobham
    (Cobham.fstBlockFn (.proj 0)) (Cobham.sndBlockFn (.proj 0)) (.const [])
  have hs : Cobham step :=
    (Cobham.comp clause_coefficient_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.comp₂ Cobham.smash (.proj 1) (.const (List.replicate 24 false)))
      (.const (List.replicate 4 false)))
    (Cobham.comp₂ Cobham.smash (.proj 0)
      (Cobham.appendFn (Cobham.comp₂ Cobham.smash (.proj 1) (.const (List.replicate 12 false)))
        (.const (List.replicate 34 false))))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((clauseCoefficientStep^[clock.length])
      (clauseCoefficientPack (pairFst (v 0)) (pairSnd (v 0)) [])).length ≤ _
    have h := clause_coefficient_clock_length clock (v 0)
    simp [ruler,Complexity.smash_length]
    nlinarith only [h]
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl
 theorem polynomial_sat_clause_coefficients_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATClauseCoefficients (v 0) :=
  (Cobham.sndBlockFn (Cobham.sndBlockFn clause_coefficient_state_cobham)).of_eq fun _ => rfl
 theorem polynomial_sat_clause_coefficients_mem_fp : polynomialSATClauseCoefficients ∈ FP :=
  CobhamFP_subset_FP polynomial_sat_clause_coefficients_cobham
#print axioms polynomial_sat_clause_coefficients_mem_fp
end IV04.Paper.Computational
