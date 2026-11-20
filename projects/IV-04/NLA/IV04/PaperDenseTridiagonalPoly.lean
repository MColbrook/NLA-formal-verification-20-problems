module

public import NLA.IV04.PaperDenseTridiagonalBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem dense_support_pack_cobham {arity : ℕ}
    {d c i j f b : (Fin arity → List Bool) → List Bool}
    (hd : Cobham d) (hc : Cobham c) (hi : Cobham i) (hj : Cobham j) (hf : Cobham f) (hb : Cobham b) :
    Cobham fun v => denseSupportPack (d v) (c v) (i v) (j v) (f v) (b v) :=
  (Cobham.comp₂ Cobham.pairing hd (Cobham.comp₂ Cobham.pairing hc
    (Cobham.comp₂ Cobham.pairing hi (Cobham.comp₂ Cobham.pairing hj
      (Cobham.comp₂ Cobham.pairing hf hb))))).of_eq fun _ => rfl

theorem dense_support_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => denseSupportInitial (v 0) := by
  have hd := Cobham.comp canonical_word_cobham fun _ : Fin 1 => Cobham.fstBlockFn (.proj (0 : Fin 1))
  have hc := Cobham.comp₂ canonical_word_multiply_cobham hd hd
  exact (dense_support_pack_cobham hd hc (.const []) (.const [])
    (Cobham.sndBlockFn (.proj 0)) (.const [true])).of_eq fun _ => rfl

set_option maxHeartbeats 2000000 in
theorem dense_support_step_cobham :
    Cobham fun v : Fin 1 → List Bool => denseSupportStep (v 0) := by
  have hd := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hc := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hi := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))
  have hj := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))))
  have hf := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))))
  have hb := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))))
  have hi' := Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.comp₂ polynomial_word_add_cobham hi (.const [true])
  have hj' := Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.comp₂ polynomial_word_add_cobham hj (.const [true])
  have hend := Cobham.comp₂ polynomial_word_le_cobham hd hj'
  have hrow := Cobham.iteFn hend hi' hi
  have hcol := Cobham.iteFn hend (.const []) hj'
  have hready := Cobham.andFn (Cobham.nonemptyFn hf) (Cobham.nonemptyFn (Cobham.sndBlockFn hf))
  have harg := Cobham.comp₂ Cobham.pairing hi (Cobham.comp₂ Cobham.pairing hj
    (Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn hf) (Cobham.fstBlockFn (Cobham.sndBlockFn hf))))
  have hvalid : Cobham fun v : Fin 1 → List Bool => tridiagonalEndpointFlag
      (denseSupportRow (v 0)) (denseSupportColumn (v 0))
      (pairFst (denseSupportFields (v 0))) (pairFst (pairSnd (denseSupportFields (v 0)))) := by
    exact (Cobham.comp encoded_tridiagonal_endpoint_flag_cobham fun _ : Fin 1 => harg).of_eq fun v => by
      simp [encodedTridiagonalEndpointFlag,denseSupportRow,denseSupportColumn,denseSupportFields]
  have hflag := Cobham.andFn hb (Cobham.andFn hready hvalid)
  have hcount := Cobham.comp decrement_count_cobham fun _ : Fin 1 => hc
  have htail := Cobham.sndBlockFn (Cobham.sndBlockFn hf)
  have hyes := dense_support_pack_cobham hd hcount hrow hcol htail hflag
  have hno := dense_support_pack_cobham hd hc hi hj hf hb
  have hnonempty := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hc)
  exact (Cobham.iteFn hnonempty hyes hno).of_eq fun _ => rfl

theorem dense_support_state_cobham :
    Cobham fun v : Fin 1 → List Bool => denseSupportState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => denseSupportInitial (v 0)
  let step : (Fin 2 → List Bool) → List Bool := fun v => denseSupportStep (v 0)
  let clockWords : (Fin 2 → List Bool) → List Bool := fun v => (List.replicate 9 (v 0)).flatten
  let inputWords : (Fin 2 → List Bool) → List Bool := fun v => (List.replicate 6 (v 1)).flatten
  let ruler : (Fin 2 → List Bool) → List Bool := fun v => clockWords v ++ inputWords v ++ List.replicate 11 false
  have hs : Cobham step :=
    (Cobham.comp dense_support_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hc : Cobham clockWords := by
    simpa [clockWords] using Cobham.appendFn (.proj (0 : Fin 2))
      (Cobham.appendFn (.proj 0) (Cobham.appendFn (.proj 0) (Cobham.appendFn (.proj 0)
        (Cobham.appendFn (.proj 0) (Cobham.appendFn (.proj 0) (Cobham.appendFn (.proj 0)
          (Cobham.appendFn (.proj 0) (.proj 0))))))))
  have ht : Cobham inputWords := by
    simpa [inputWords] using Cobham.appendFn (.proj (1 : Fin 2))
      (Cobham.appendFn (.proj 1) (Cobham.appendFn (.proj 1) (Cobham.appendFn (.proj 1)
        (Cobham.appendFn (.proj 1) (.proj 1)))))
  have hr : Cobham ruler := Cobham.appendFn (Cobham.appendFn hc ht) (.const (List.replicate 11 false))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤ (ruler (Fin.cons clock v)).length := by
    intro clock v
    have h := dense_support_initial_iterate_length clock.length (v 0)
    change ((denseSupportStep^[clock.length]) (denseSupportInitial (v 0))).length ≤ _
    simp [ruler,clockWords,inputWords]
    omega
  have hit := Cobham.iterFn dense_support_initial_cobham hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i;fin_cases i <;> simpa [args] using (Cobham.proj (0 : Fin 1))
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

theorem encoded_dense_tridiagonal_support_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedDenseTridiagonalSupport (v 0) := by
  have hs := dense_support_state_cobham
  have hc := Cobham.fstBlockFn (Cobham.sndBlockFn hs)
  have hf := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn hs))))
  have hb := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn hs))))
  have hn := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hc)
  exact (Cobham.comp₂ Cobham.pairing (Cobham.iteFn hn (.const [false]) hb) hf).of_eq fun _ => rfl

theorem encoded_dense_tridiagonal_support_mem_fp : encodedDenseTridiagonalSupport ∈ FP :=
  CobhamFP_subset_FP encoded_dense_tridiagonal_support_cobham

#print axioms encoded_dense_tridiagonal_support_mem_fp
end IV04.Paper.Computational
