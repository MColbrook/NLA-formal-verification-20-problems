module

public import NLA.IV04.PaperBoundedPayloadMapPoly
public import NLA.IV04.PaperEncoding
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
private theorem bounded_map_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr];exact IV04.Paper.bits_foldr n
 theorem bounded_payload_map_step_nat (f : List Bool → List Bool) (i bound : ℕ)
    (query output : List Bool) :
    boundedPayloadMapStep f (variableMarkerPack i.bits bound.bits query output)=
      if i<bound then variableMarkerPack (i+1).bits bound.bits query
        (f (pair query i.bits) ++ output)
      else variableMarkerPack i.bits bound.bits query output := by
  rw [bounded_payload_map_step_pair,polynomial_word_le_value]
  simp only [bounded_map_bits_value]
  by_cases h : i<bound
  · simp [h,Nat.not_le_of_gt h,notBit,caseBit₀,canonical_word_eq_bits,
      polynomial_word_add_value,bounded_map_bits_value,wordValue,bitValue]
  · simp [h,Nat.le_of_not_gt h,notBit,caseBit₀]
 theorem bounded_payload_map_iterate_inactive (f : List Bool → List Bool) (k i bound : ℕ)
    (query output : List Bool) (h : bound ≤ i) :
    ((boundedPayloadMapStep f)^[k]) (variableMarkerPack i.bits bound.bits query output)=
      variableMarkerPack i.bits bound.bits query output := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,bounded_payload_map_step_nat]
    simp [Nat.not_lt.mpr h]
 theorem bounded_payload_map_iteration_prefix (f : List Bool → List Bool)
    (query : List Bool) (k bound : ℕ) (hk : k ≤ bound) :
    ((boundedPayloadMapStep f)^[k]) (variableMarkerPack (0 : ℕ).bits bound.bits query [])=
      variableMarkerPack k.bits bound.bits query
        ((List.range k).reverse.flatMap (fun i => f (pair query i.bits))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih (by omega),bounded_payload_map_step_nat]
    have h : k<bound := by omega
    simp [h,List.range_succ,List.reverse_append,List.flatMap_append]
 theorem polynomial_bounded_payload_map_exact (f : List Bool → List Bool)
    (ruler query : List Bool) (bound : ℕ) (h : bound ≤ ruler.length+1) :
    polynomialBoundedPayloadMap f (pair ruler (pair bound.bits query))=
      (List.range bound).reverse.flatMap (fun i => f (pair query i.bits)) := by
  have hs : ((boundedPayloadMapStep f)^[ruler.length+1])
      (variableMarkerPack (0 : ℕ).bits bound.bits query [])=
      variableMarkerPack bound.bits bound.bits query
        ((List.range bound).reverse.flatMap (fun i => f (pair query i.bits))) := by
    have he : ruler.length+1=(ruler.length+1-bound)+bound := by omega
    rw [he,Function.iterate_add_apply,
      bounded_payload_map_iteration_prefix f query bound bound (le_refl _),
      bounded_payload_map_iterate_inactive f (ruler.length+1-bound) bound bound query _ (le_refl _)]
  have hz : (0 : ℕ).bits=[] := rfl
  simpa only [polynomialBoundedPayloadMap,boundedPayloadMapState,pairFst_pair,pairSnd_pair,
    variableMarkerPack,hz] using congrArg (fun s => pairSnd (pairSnd (pairSnd s))) hs
 theorem polynomial_bounded_payload_map_length (f : List Bool → List Bool) (p : Polynomial ℕ)
    (hf : ∀ x, (f x).length ≤ p.eval x.length) (input : List Bool) :
    (polynomialBoundedPayloadMap f input).length ≤
      2*input.length+6+(2*p.eval (4*input.length+4)+6)*(input.length+1) := by
  have hc := pairFst_length_le input
  have hs := bounded_payload_map_clock_bound f p hf input ((pairFst input).length+1) (by omega)
  have hm := Nat.mul_le_mul_left (2*p.eval (4*input.length+4)+6)
    (show (pairFst input).length+1 ≤ input.length+1 by omega)
  have hp := pairSnd_length_le (boundedPayloadMapState f input)
  have hq := pairSnd_length_le (pairSnd (boundedPayloadMapState f input))
  have hr := pairSnd_length_le (pairSnd (pairSnd (boundedPayloadMapState f input)))
  unfold polynomialBoundedPayloadMap
  unfold boundedPayloadMapState at hp hq hr ⊢
  omega
 theorem bounded_payload_map_actual_polytime (f : List Bool → List Bool) (hf : f ∈ FP) :
    polynomialBoundedPayloadMap f ∈ FP ∧
    (∃ p : Polynomial ℕ, ∀ input, (polynomialBoundedPayloadMap f input).length ≤
      2*input.length+6+(2*p.eval (4*input.length+4)+6)*(input.length+1)) ∧
    (∀ (ruler query : List Bool) (bound : ℕ), bound ≤ ruler.length+1 →
      polynomialBoundedPayloadMap f (pair ruler (pair bound.bits query))=
        (List.range bound).reverse.flatMap (fun i => f (pair query i.bits))) := by
  obtain ⟨p,hp⟩ := Cobham.output_length_poly_of_mem_FP hf
  exact ⟨polynomial_bounded_payload_map_mem_fp f hf,⟨p,polynomial_bounded_payload_map_length f p hp⟩,
    polynomial_bounded_payload_map_exact f⟩
#print axioms polynomial_bounded_payload_map_exact
#print axioms bounded_payload_map_actual_polytime
end IV04.Paper.Computational
