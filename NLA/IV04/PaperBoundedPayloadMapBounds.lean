module

public import NLA.IV04.PaperBoundedPayloadMapDefinitions
public import NLA.IV04.PaperSATVariableMarkersBounds
public import NLA.IV04.Complexitylib.Classes.P.Iterate
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
theorem bounded_payload_map_step_pair (f : List Bool → List Bool)
    (index bound query output : List Bool) :
    boundedPayloadMapStep f (variableMarkerPack index bound query output)=
      caseBit₀ (notBit (polynomialWordLe bound index))
        (variableMarkerPack (canonicalWord (polynomialWordAdd index [true])) bound query
          (f (pair query index) ++ output)) (variableMarkerPack index bound query output) := by
  simp only [boundedPayloadMapStep,variableMarkerPack,pairFst_pair,pairSnd_pair]
theorem bounded_payload_map_step_shape (f : List Bool → List Bool)
    (index bound query output : List Bool) :
    ∃ i o : List Bool, boundedPayloadMapStep f (variableMarkerPack index bound query output)=
      variableMarkerPack i bound query o ∧ i.length ≤ index.length+2 ∧
      o.length ≤ output.length+2*(f (pair query index)).length+2 := by
  rw [bounded_payload_map_step_pair]
  by_cases hl : wordValue bound ≤ wordValue index
  · refine ⟨index,output,?_,by omega,by omega⟩
    simp [polynomial_word_le_value,hl,notBit,caseBit₀]
  · refine ⟨canonicalWord (polynomialWordAdd index [true]),f (pair query index) ++ output,?_,?_,?_⟩
    · simp [polynomial_word_le_value,hl,notBit,caseBit₀]
    · have hc := canonical_word_length (polynomialWordAdd index [true])
      have ha := polynomial_word_add_length index [true]
      simp only [List.length_cons,List.length_nil] at ha
      omega
    · simp only [List.length_append];omega
theorem bounded_payload_map_iteration_bound (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hf : ∀ x, (f x).length ≤ p.eval x.length) (n k : ℕ)
    (bound query : List Bool) (hq : query.length ≤ n) (hk : k ≤ n+1) :
    ∃ i o : List Bool,
      ((boundedPayloadMapStep f)^[k]) (variableMarkerPack [] bound query [])=
        variableMarkerPack i bound query o ∧
      i.length ≤ 2*k ∧ o.length ≤ (2*p.eval (4*n+4)+2)*k := by
  induction k with
  | zero => exact ⟨[],[],rfl,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨i,o,he,hi,ho⟩ := ih (by omega)
    obtain ⟨i',o',hs,hi',ho'⟩ := bounded_payload_map_step_shape f i bound query o
    have ha : (pair query i).length ≤ 4*n+4 := by
      simp only [pair_length];omega
    have hv := (hf (pair query i)).trans (polynomial_eval_mono_nat p ha)
    refine ⟨i',o',?_,by omega,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · nlinarith
theorem bounded_payload_map_clock_bound (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hf : ∀ x, (f x).length ≤ p.eval x.length) (input : List Bool) (k : ℕ)
    (hk : k ≤ input.length+1) :
    (((boundedPayloadMapStep f)^[k])
      (variableMarkerPack [] (pairFst (pairSnd input)) (pairSnd (pairSnd input)) [])).length ≤
        2*input.length+6+(2*p.eval (4*input.length+4)+6)*k := by
  have hq := pairSnd_length_le input
  have hp := pair_projection_budget (pairSnd input)
  have hc := pairSnd_length_le (pairSnd input)
  obtain ⟨i,o,he,hi,ho⟩ := bounded_payload_map_iteration_bound f p hf input.length k
    (pairFst (pairSnd input)) (pairSnd (pairSnd input)) (by omega) hk
  rw [he,variable_marker_pack_length]
  nlinarith
theorem bounded_payload_map_bound_poly (p : Polynomial ℕ) :
    PolyBound fun n => 2*n+6+(2*p.eval (4*n+4)+6)*(n+1) := by
  have he : PolyBound fun n => p.eval (4*n+4) :=
    ⟨p.comp (Polynomial.C 4 * Polynomial.X + Polynomial.C 4),fun n => by simp⟩
  exact ((PolyBound.const 2).mul PolyBound.id).add (PolyBound.const 6) |>.add
    ((((PolyBound.const 2).mul he).add (PolyBound.const 6)).mul
      (PolyBound.id.add (PolyBound.const 1)))
#print axioms bounded_payload_map_clock_bound
end IV04.Paper.Computational
