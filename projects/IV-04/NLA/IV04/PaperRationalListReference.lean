module

public import NLA.IV04.PaperRationalListParserDefinitions
public import NLA.IV04.PaperRationalParserBounds
public import NLA.IV04.PaperEncoding
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem read_rational_consumes_bits (input : List Bool) (q : ℚ) (tail : List Bool)
    (h : IV04.Paper.readRational input=some (q,tail)) : tail.length+3 ≤ input.length := by
  rw [←rational_parser_exact] at h
  obtain hf | hf := rational_parser_flag_boolean input
  · simp only [hf,eq_self_iff_true,if_true] at h
    have he := congrArg Prod.snd (Option.some.inj h)
    change Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input))=tail at he
    have hb := rational_parser_success_budget input hf
    rw [he] at hb
    omega
  · simp [hf] at h

theorem fuel_read_rationals_exact (fuel count : ℕ) (input : List Bool)
    (h : input.length ≤ fuel) : fuelReadRationals fuel count input=readRationals count input := by
  induction fuel generalizing count input with
  | zero =>
    have he : input=[] := List.eq_nil_of_length_eq_zero (by omega)
    cases count <;> simp [he,fuelReadRationals,readRationals,IV04.Paper.readRational]
  | succ fuel ih =>
    cases count with
    | zero => rfl
    | succ count =>
      cases hr : IV04.Paper.readRational input with
      | none => simp [fuelReadRationals,readRationals,hr]
      | some parsed =>
        obtain ⟨q,tail⟩ := parsed
        have hb := read_rational_consumes_bits input q tail hr
        have ht : tail.length ≤ fuel := by omega
        simp [fuelReadRationals,readRationals,hr,ih count tail ht]

#print axioms fuel_read_rationals_exact
end IV04.Paper.Computational
