module

public import NLA.IV04.PaperPayloadWordMaxDefinitions
public import NLA.IV04.PaperWordComparisonPoly
public import NLA.IV04.PaperWordListProductBounds
public import NLA.IV04.PaperCanonicalWord
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

 theorem polynomial_word_max_length (left right : List Bool) :
    (polynomialWordMax left right).length ≤ left.length+right.length := by
  by_cases h : wordValue left ≤ wordValue right
  · simp [polynomialWordMax,polynomial_word_le_value,h,caseBit₀,caseBit]
  · simp [polynomialWordMax,polynomial_word_le_value,h,caseBit₀,caseBit]

 theorem payload_word_max_step_pair (select : List Bool → List Bool) (rest maximum : List Bool) :
    payloadWordMaxStep select (pair rest maximum)=
      if rest=[] then pair rest maximum else pair (pairSnd rest)
        (polynomialWordMax maximum (select (pairFst rest))) := by
  simp only [payloadWordMaxStep,pairFst_pair,pairSnd_pair]
  cases rest <;> simp [nonemptyFlag,caseBit₀,caseBit]

 theorem payload_word_max_step_shape (select : List Bool → List Bool) (d : ℕ)
    (hselect : ∀ input, (select input).length ≤ 2*input.length+d) (rest maximum : List Bool) :
    ∃ r m : List Bool, payloadWordMaxStep select (pair rest maximum)=pair r m ∧
      (pair r m).length ≤ (pair rest maximum).length+d := by
  rw [payload_word_max_step_pair]
  split_ifs
  · exact ⟨rest,maximum,rfl,by omega⟩
  · refine ⟨_,_,rfl,?_⟩
    have hp := pair_projection_budget rest
    have hs := hselect (pairFst rest)
    have hm := polynomial_word_max_length maximum (select (pairFst rest))
    simp only [pair_length]
    omega

 theorem payload_word_max_iterate_shape (select : List Bool → List Bool) (d : ℕ)
    (hselect : ∀ input, (select input).length ≤ 2*input.length+d)
    (k : ℕ) (rest maximum : List Bool) :
    ∃ r m : List Bool, ((payloadWordMaxStep select)^[k]) (pair rest maximum)=pair r m ∧
      (pair r m).length ≤ (pair rest maximum).length+d*k := by
  induction k with
  | zero => exact ⟨rest,maximum,rfl,by simp⟩
  | succ k ih =>
    obtain ⟨r,m,he,hb⟩ := ih
    obtain ⟨r',m',hs,hl⟩ := payload_word_max_step_shape select d hselect r m
    refine ⟨r',m',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · rw [Nat.mul_succ];omega

 theorem payload_word_max_clock_length (select : List Bool → List Bool) (d : ℕ)
    (hselect : ∀ input, (select input).length ≤ 2*input.length+d) (clock input : List Bool) :
    (((payloadWordMaxStep select)^[clock.length]) (pair input [])).length ≤
      2*input.length+2+d*clock.length := by
  obtain ⟨r,m,he,hb⟩ := payload_word_max_iterate_shape select d hselect clock.length input []
  rw [he]
  simpa only [pair_length,List.length_nil,Nat.add_zero] using hb

 theorem polynomial_payload_word_max_length (select : List Bool → List Bool) (d : ℕ)
    (hselect : ∀ input, (select input).length ≤ 2*input.length+d) (input : List Bool) :
    (polynomialPayloadWordMax select input).length ≤ 2*input.length+2+d*input.length := by
  have hc := canonical_word_length (pairSnd (payloadWordMaxState select input))
  have hp := pairSnd_length_le (payloadWordMaxState select input)
  have hs := payload_word_max_clock_length select d hselect input input
  change (canonicalWord (pairSnd (payloadWordMaxState select input))).length ≤ _
  unfold payloadWordMaxState at hp hc ⊢
  omega

end IV04.Paper.Computational
