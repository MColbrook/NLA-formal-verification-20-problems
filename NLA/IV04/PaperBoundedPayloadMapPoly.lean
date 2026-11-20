module

public import NLA.IV04.PaperBoundedPayloadMapBounds
public import NLA.IV04.PaperSATLiteralDigitsPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational
theorem bounded_payload_map_step_cobham (f : List Bool → List Bool) (hf : f ∈ FP) :
    Cobham fun v : Fin 1 → List Bool => boundedPayloadMapStep f (v 0) := by
  have hi := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have hb := sat_literal_cobham_fst _ (sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0))
  have hq := sat_literal_cobham_fst _ (sat_literal_cobham_snd _
    (sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0)))
  have ho := sat_literal_cobham_snd _ (sat_literal_cobham_snd _
    (sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0)))
  have hn := sat_literal_cobham_unary canonicalWord canonical_word_cobham _
    (sat_literal_cobham_binary polynomialWordAdd polynomial_word_add_cobham
      _ (fun _ : Fin 1 → List Bool => [true]) hi (.const [true]))
  have hv := sat_literal_cobham_unary f (FP_subset_CobhamFP hf) _
    (sat_literal_cobham_binary pair Cobham.pairing _ _ hq hi)
  exact (Cobham.iteFn
    (Cobham.notFn (sat_literal_cobham_binary polynomialWordLe polynomial_word_le_cobham _ _ hb hi))
    (variable_marker_pack_cobham hn hb hq (Cobham.appendFn hv ho))
    (.proj 0)).of_eq fun _ => rfl
theorem bounded_payload_map_state_mem_fp (f : List Bool → List Bool) (hf : f ∈ FP) :
    boundedPayloadMapState f ∈ FP := by
  let initial : List Bool → List Bool := fun input =>
    variableMarkerPack [] (pairFst (pairSnd input)) (pairSnd (pairSnd input)) []
  let ruler : List Bool → List Bool := fun input => false::pairFst input
  have hi : initial ∈ FP := CobhamFP_subset_FP (variable_marker_pack_cobham (.const [])
    (sat_literal_cobham_fst _ (sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0)))
    (sat_literal_cobham_snd _ (sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0)))
    (.const []))
  have hr : ruler ∈ FP := CobhamFP_subset_FP ((Cobham.comp (Cobham.bit false)
    (fun _ : Fin 1 => sat_literal_cobham_fst (fun v : Fin 1 → List Bool => v 0) (.proj 0))).of_eq fun _ => rfl)
  obtain ⟨p,hp⟩ := Cobham.output_length_poly_of_mem_FP hf
  have hbound : ∀ input, ∀ k ≤ (ruler input).length,
      (((boundedPayloadMapStep f)^[k]) (initial input)).length ≤
        2*input.length+6+(2*p.eval (4*input.length+4)+6)*(input.length+1) := by
    intro input k hk
    have hl := pairFst_length_le input
    have hc : k ≤ input.length+1 := by simp only [ruler,List.length_cons] at hk;omega
    have hs := bounded_payload_map_clock_bound f p hp input k hc
    have hm := Nat.mul_le_mul_left (2*p.eval (4*input.length+4)+6) hc
    exact hs.trans (by omega)
  have hit := iterate_mem_FP_of_polyBound
    (CobhamFP_subset_FP (bounded_payload_map_step_cobham f hf)) hi hr
    (bounded_payload_map_bound_poly p) hbound
  change (fun input => ((boundedPayloadMapStep f)^[(pairFst input).length+1])
    (variableMarkerPack [] (pairFst (pairSnd input)) (pairSnd (pairSnd input)) [])) ∈ FP
  simpa only [ruler,List.length_cons,initial] using hit
theorem polynomial_bounded_payload_map_mem_fp (f : List Bool → List Bool) (hf : f ∈ FP) :
    polynomialBoundedPayloadMap f ∈ FP :=
  CobhamFP_subset_FP ((Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn
    (FP_subset_CobhamFP (bounded_payload_map_state_mem_fp f hf))))).of_eq fun _ => rfl)
#print axioms polynomial_bounded_payload_map_mem_fp
end IV04.Paper.Computational
