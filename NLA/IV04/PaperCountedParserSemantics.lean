module

public import NLA.IV04.PaperCountedParserDefinitions
public import NLA.IV04.PaperNaturalParserSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem natural_parser_payload_length (input : List Bool) :
    (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))).length ≤ input.length := by
  rw [natural_parser_payload]
  simp only [List.length_take,naturalParseRest,List.length_tail,List.length_drop]
  omega

theorem natural_parser_tail_length (input : List Bool) :
    (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))).length ≤ input.length := by
  rw [natural_parser_tail]
  simp only [List.length_drop,naturalParseRest,List.length_tail,List.length_drop]
  omega

theorem read_natural_consumes_bit (input tail : List Bool) (value : ℕ)
    (h : IV04.Paper.readNatural input=some (value,tail)) : tail.length < input.length := by
  rw [read_natural_stages] at h
  split_ifs at h with he hn
  have hp := Option.some.inj h
  have ht := congrArg Prod.snd hp
  change (naturalParseRest input).drop (headerWord input).length = tail at ht
  have hd : (input.drop (headerWord input).length).length > 0 := by
    cases hh : input.drop (headerWord input).length with
    | nil => exact (he hh).elim
    | cons b bits => simp
  simp only [List.length_drop] at hd
  rw [←ht]
  simp only [naturalParseRest,List.length_drop,List.length_tail]
  omega

theorem fuel_read_naturals_exact (fuel count : ℕ) (input : List Bool)
    (h : input.length ≤ fuel) :
    fuelReadNaturals fuel count input=IV04.Paper.readNaturals count input := by
  induction fuel generalizing count input with
  | zero =>
    have hi : input=[] := by cases input <;> simp_all
    cases count <;> simp [fuelReadNaturals,IV04.Paper.readNaturals,IV04.Paper.readNatural,
      IV04.Paper.readUnary,hi]
  | succ fuel ih =>
    cases count with
    | zero => rfl
    | succ count =>
      cases hp : IV04.Paper.readNatural input with
      | none => simp [fuelReadNaturals,IV04.Paper.readNaturals,hp]
      | some parsed =>
        obtain ⟨value,tail⟩ := parsed
        have ht := read_natural_consumes_bit input tail value hp
        have he := ih count tail (by omega)
        simp [fuelReadNaturals,IV04.Paper.readNaturals,hp,he]

theorem bounded_read_integer_weights_exact (input : List Bool) :
    boundedReadIntegerWeights input=IV04.Paper.readIntegerWeights input := by
  cases hp : IV04.Paper.readNatural input with
  | none => simp [boundedReadIntegerWeights,IV04.Paper.readIntegerWeights,hp]
  | some parsed =>
    obtain ⟨count,tail⟩ := parsed
    have ht := read_natural_consumes_bit input tail count hp
    have he := fuel_read_naturals_exact input.length count tail (by omega)
    simp [boundedReadIntegerWeights,IV04.Paper.readIntegerWeights,hp,he]

#print axioms bounded_read_integer_weights_exact
end IV04.Paper.Computational
