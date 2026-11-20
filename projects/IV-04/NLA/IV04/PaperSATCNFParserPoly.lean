module

public import NLA.IV04.PaperSATCNFParserBounds
public import NLA.IV04.PaperPayloadReversePoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

private theorem sat_cnf_pack_fn {n : ℕ}
    {r u c f v : (Fin n → List Bool) → List Bool}
    (hr : Cobham r) (hu : Cobham u) (hc : Cobham c) (hf : Cobham f) (hv : Cobham v) :
    Cobham fun w => satCNFPack (r w) (u w) (c w) (f w) (v w) :=
  (Cobham.comp₂ Cobham.pairing hr (Cobham.comp₂ Cobham.pairing hu
    (Cobham.comp₂ Cobham.pairing hc (Cobham.comp₂ Cobham.pairing hf hv)))).of_eq fun _ => rfl

 theorem sat_cnf_parse_step_cobham :
    Cobham fun v : Fin 1 → List Bool => satCNFParseStep (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hu := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hc := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))
  have hf := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))))
  have hv := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))))
  have hn := Cobham.tailFn (Cobham.tailFn hr)
  have hp := Cobham.comp polynomial_sat_raw_literal_cobham fun _ : Fin 1 => hu
  have hd := sat_cnf_pack_fn hn (Cobham.appendFn hu (Cobham.headFlagFn hr)) hc hf hv
  have hl := sat_cnf_pack_fn hn (Cobham.const [])
    (Cobham.comp₂ Cobham.pairing (Cobham.sndBlockFn hp) hc) hf
    (Cobham.andFn hv (Cobham.fstBlockFn hp))
  have hz := sat_cnf_pack_fn hn (Cobham.const []) (Cobham.const [])
    (Cobham.comp₂ Cobham.pairing hc hf) (Cobham.andFn hv (Cobham.notFn (Cobham.nonemptyFn hu)))
  have ho := sat_cnf_pack_fn (Cobham.const []) hu hc hf (Cobham.const [false])
  have ht := Cobham.iteFn (Cobham.headFlagFn hr)
    (Cobham.iteFn (Cobham.headFlagFn (Cobham.tailFn hr)) hd hz)
    (Cobham.iteFn (Cobham.headFlagFn (Cobham.tailFn hr)) hl hd)
  exact (Cobham.iteFn (Cobham.nonemptyFn hr)
    (Cobham.iteFn (Cobham.nonemptyFn (Cobham.tailFn hr)) ht ho) (.proj 0)).of_eq fun _ => rfl

 theorem sat_cnf_parse_state_cobham :
    Cobham fun v : Fin 1 → List Bool => satCNFParseState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool := fun v => satCNFPack (v 0) [] [] [] [true]
  let step : (Fin 2 → List Bool) → List Bool := fun v => satCNFParseStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ List.replicate 9 false ++ smash (v 0) (List.replicate 40 false)
  have hi : Cobham initial := sat_cnf_pack_fn (.proj 0) (.const []) (.const []) (.const []) (.const [true])
  have hs : Cobham step :=
    (Cobham.comp sat_cnf_parse_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1)) (.const (List.replicate 9 false)))
    (Cobham.comp₂ Cobham.smash (.proj 0) (.const (List.replicate 40 false)))
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((satCNFParseStep^[clock.length]) (satCNFPack (v 0) [] [] [] [true])).length ≤ _
    have h := sat_cnf_parse_clock_length clock (v 0)
    simp [ruler,smash_length]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have hargs : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit hargs).of_eq fun _ => rfl

 theorem polynomial_sat_cnf_parse_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATCNFParse (v 0) := by
  have hr := Cobham.fstBlockFn sat_cnf_parse_state_cobham
  have hu := Cobham.fstBlockFn (Cobham.sndBlockFn sat_cnf_parse_state_cobham)
  have hc := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn sat_cnf_parse_state_cobham))
  have hf := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn sat_cnf_parse_state_cobham)))
  have hv := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn sat_cnf_parse_state_cobham)))
  have hvalid := Cobham.andFn hv (Cobham.andFn (Cobham.notFn (Cobham.nonemptyFn hr))
    (Cobham.andFn (Cobham.notFn (Cobham.nonemptyFn hu)) (Cobham.notFn (Cobham.nonemptyFn hc))))
  have hrev : Cobham fun v : Fin 1 → List Bool => polynomialPayloadReverse (v 0) :=
    FP_subset_CobhamFP polynomial_payload_reverse_mem_fp
  exact (Cobham.comp₂ Cobham.pairing hvalid (Cobham.comp hrev fun _ : Fin 1 => hf)).of_eq fun _ => rfl

 theorem polynomial_sat_cnf_parse_mem_fp : polynomialSATCNFParse ∈ FP :=
  CobhamFP_subset_FP polynomial_sat_cnf_parse_cobham

#print axioms polynomial_sat_cnf_parse_mem_fp
end IV04.Paper.Computational
