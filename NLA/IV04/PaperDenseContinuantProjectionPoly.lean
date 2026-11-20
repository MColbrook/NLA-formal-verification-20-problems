module

public import NLA.IV04.PaperDenseContinuantProjectionBounds
public import NLA.IV04.PaperPayloadLookupPoly
public import NLA.IV04.PaperPayloadReversePoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem row_projection_row_cobham :
    Cobham fun v : Fin 3 → List Bool => rowProjectionRow (v 0) (v 1) (v 2) := by
  have hd := Cobham.proj (0 : Fin 3)
  have hi := Cobham.proj (1 : Fin 3)
  have hf := Cobham.proj (2 : Fin 3)
  have hm := Cobham.comp₂ canonical_word_multiply_cobham hi hd
  have hp := Cobham.comp decrement_count_cobham fun _ : Fin 1 => hi
  have hdiag := Cobham.comp canonical_word_cobham fun _ : Fin 1 => Cobham.comp₂ polynomial_word_add_cobham hm hi
  have hlow := Cobham.comp canonical_word_cobham fun _ : Fin 1 => Cobham.comp₂ polynomial_word_add_cobham hm hp
  have hupper := Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.comp₂ polynomial_word_add_cobham (Cobham.comp₂ canonical_word_multiply_cobham hp hd) hi
  have hD := Cobham.comp polynomial_payload_lookup_cobham fun _ : Fin 1 => Cobham.comp₂ Cobham.pairing hdiag hf
  have hL := Cobham.comp polynomial_payload_lookup_cobham fun _ : Fin 1 => Cobham.comp₂ Cobham.pairing hlow hf
  have hU := Cobham.comp polynomial_payload_lookup_cobham fun _ : Fin 1 => Cobham.comp₂ Cobham.pairing hupper hf
  have hn := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hi)
  exact (Cobham.comp₂ Cobham.pairing hD (Cobham.comp₂ Cobham.pairing
    (Cobham.iteFn hn hL (.const [false])) (Cobham.iteFn hn hU (.const [false])))).of_eq fun _ => rfl

theorem row_projection_step_cobham :
    Cobham fun v : Fin 1 → List Bool => rowProjectionStep (v 0) := by
  have hd := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hi := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hf := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))
  have ho := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))
  have hinc := Cobham.comp canonical_word_cobham fun _ : Fin 1 => Cobham.comp₂ polynomial_word_add_cobham hi (.const [true])
  let args : Fin 3 → (Fin 1 → List Bool) → List Bool := ![
    fun v => pairFst (v 0),fun v => pairFst (pairSnd (v 0)),fun v => pairFst (pairSnd (pairSnd (v 0)))]
  have ha : ∀ i, Cobham (args i) := by
    intro i;fin_cases i
    · exact hd
    · exact hi
    · exact hf
  have hrow := Cobham.comp row_projection_row_cobham ha
  have hyes := Cobham.comp₂ Cobham.pairing hd (Cobham.comp₂ Cobham.pairing hi (Cobham.comp₂ Cobham.pairing hf ho))
  have hno := Cobham.comp₂ Cobham.pairing hd (Cobham.comp₂ Cobham.pairing hinc
    (Cobham.comp₂ Cobham.pairing hf (Cobham.comp₂ Cobham.pairing hrow ho)))
  exact (Cobham.iteFn (Cobham.comp₂ polynomial_word_le_cobham hd hi) hyes hno).of_eq fun _ => rfl

theorem row_projection_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => rowProjectionInitial (v 0) := by
  have hd := Cobham.comp canonical_word_cobham fun _ : Fin 1 => Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  exact (Cobham.comp₂ Cobham.pairing hd (Cobham.comp₂ Cobham.pairing (.const [])
    (Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))) (.const [])))).of_eq fun _ => rfl

theorem row_projection_copies_cobham {arity : ℕ} {f : (Fin arity → List Bool) → List Bool}
    (k : ℕ) (hf : Cobham f) : Cobham fun v => (List.replicate k (f v)).flatten := by
  induction k with
  | zero => exact Cobham.const []
  | succ k ih => simpa only [List.replicate_succ,List.flatten_cons] using Cobham.appendFn hf ih

theorem row_projection_copies_length (k : ℕ) (word : List Bool) :
    ((List.replicate k word).flatten).length=k*word.length := by
  induction k with
  | zero => simp only [List.replicate_zero,List.flatten_nil,List.length_nil,Nat.zero_mul]
  | succ k ih =>
    simp only [List.replicate_succ,List.flatten_cons,List.length_append,ih,Nat.succ_mul]
    omega

theorem row_projection_state_cobham :
    Cobham fun v : Fin 1 → List Bool => rowProjectionState (v 0) := by
  let step : (Fin 2 → List Bool) → List Bool := fun v => rowProjectionStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    Complexity.smash ((List.replicate 10 (v 0)).flatten) (v 1) ++
    (List.replicate 20 (v 0)).flatten ++ (List.replicate 2 (v 1)).flatten ++ List.replicate 6 false
  have hs : Cobham step := (Cobham.comp row_projection_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn (Cobham.appendFn
    (Cobham.appendFn (Cobham.comp₂ Cobham.smash (row_projection_copies_cobham 10 (.proj 0)) (.proj 1))
      (row_projection_copies_cobham 20 (.proj 0))) (row_projection_copies_cobham 2 (.proj 1))) (.const (List.replicate 6 false))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun state => step (Fin.cons state v))^[clock.length] (rowProjectionInitial (v 0))).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((rowProjectionStep^[clock.length]) (rowProjectionInitial (v 0))).length ≤ _
    have he : (ruler (Fin.cons clock v)).length=
        2*(v 0).length+6+(10*(v 0).length+20)*clock.length := by
      change (Complexity.smash ((List.replicate 10 clock).flatten) (v 0) ++
        (List.replicate 20 clock).flatten ++ (List.replicate 2 (v 0)).flatten ++ List.replicate 6 false).length=_
      simp only [List.length_append,Complexity.smash_length,
        row_projection_copies_length,List.length_replicate]
      ring
    rw [he]
    exact row_projection_initial_iterate_length clock.length (v 0)
  have hit := Cobham.iterFn row_projection_initial_cobham hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by intro i;fin_cases i <;> simpa [args] using Cobham.proj (0 : Fin 1)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

theorem polynomial_dense_continuant_rows_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialDenseContinuantRows (v 0) := by
  have hout := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn row_projection_state_cobham))
  exact (Cobham.comp polynomial_payload_reverse_cobham fun _ : Fin 1 => hout).of_eq fun _ => rfl

theorem polynomial_dense_continuant_rows_mem_fp : polynomialDenseContinuantRows ∈ FP :=
  CobhamFP_subset_FP polynomial_dense_continuant_rows_cobham

#print axioms polynomial_dense_continuant_rows_mem_fp
end IV04.Paper.Computational
