module

public import NLA.IV04.PaperSATLiteralMatchBounds
public import NLA.IV04.PaperWordComparisonPoly
public import NLA.IV04.PaperCanonicalWord
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

 theorem literal_match_flag_cobham :
    Cobham fun v : Fin 2 → List Bool => literalMatchFlag (v 0) (v 1) := by
  have hl := Cobham.fstBlockFn (Cobham.proj (0 : Fin 2))
  have hq := Cobham.fstBlockFn (Cobham.proj (1 : Fin 2))
  have he := Cobham.andFn (Cobham.comp₂ polynomial_word_le_cobham hl hq)
    (Cobham.comp₂ polynomial_word_le_cobham hq hl)
  have hs := Cobham.notFn (xor_flag_cobham
    (Cobham.headFlagFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 2))))
    (Cobham.headFlagFn (Cobham.sndBlockFn (Cobham.proj (1 : Fin 2)))))
  exact (Cobham.andFn he hs).of_eq fun _ => rfl

 theorem literal_match_pack_cobham {n : ℕ}
    {rest count query : (Fin n → List Bool) → List Bool}
    (hr : Cobham rest) (hc : Cobham count) (hq : Cobham query) :
    Cobham fun v => literalMatchPack (rest v) (count v) (query v) :=
  (Cobham.comp₂ Cobham.pairing hr (Cobham.comp₂ Cobham.pairing hc hq)).of_eq fun _ => rfl

 theorem literal_match_step_cobham :
    Cobham fun v : Fin 1 → List Bool => literalMatchStep (v 0) := by
  have hr := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hc := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hq := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hm := Cobham.comp₂ literal_match_flag_cobham (Cobham.fstBlockFn hr) hq
  have hn := Cobham.iteFn hm (Cobham.comp₂ polynomial_word_add_cobham hc (Cobham.const [true])) hc
  exact (Cobham.iteFn (Cobham.nonemptyFn hr)
    (literal_match_pack_cobham (Cobham.sndBlockFn hr) hn hq) (.proj 0)).of_eq fun _ => rfl

 theorem literal_match_state_cobham :
    Cobham fun v : Fin 1 → List Bool => literalMatchState (v 0) := by
  let initial : (Fin 1 → List Bool) → List Bool :=
    fun v => literalMatchPack (pairFst (v 0)) [] (pairSnd (v 0))
  let step : (Fin 2 → List Bool) → List Bool := fun v => literalMatchStep (v 0)
  let ruler : (Fin 2 → List Bool) → List Bool := fun v =>
    v 1 ++ v 1 ++ List.replicate 4 false ++ v 0 ++ v 0 ++ v 0 ++ v 0
  have hi : Cobham initial := literal_match_pack_cobham
    (Cobham.fstBlockFn (.proj 0)) (.const []) (Cobham.sndBlockFn (.proj 0))
  have hs : Cobham step :=
    (Cobham.comp literal_match_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham ruler := Cobham.appendFn (Cobham.appendFn (Cobham.appendFn
    (Cobham.appendFn (Cobham.appendFn (Cobham.appendFn (.proj 1) (.proj 1))
      (.const (List.replicate 4 false))) (.proj 0)) (.proj 0)) (.proj 0)) (.proj 0)
  have hb : ∀ (clock : List Bool) (v : Fin 1 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((literalMatchStep^[clock.length]) (literalMatchPack (pairFst (v 0)) [] (pairSnd (v 0)))).length ≤ _
    have h := literal_match_clock_length clock (v 0)
    simp [ruler]
    omega
  have hit := Cobham.iterFn hi hs hr hb
  let args : Fin 2 → (Fin 1 → List Bool) → List Bool := ![fun v => v 0,fun v => v 0]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i <;> simpa [args] using (Cobham.proj 0 : Cobham fun v : Fin 1 → List Bool => v 0)
  exact (Cobham.comp hit ha).of_eq fun _ => rfl

 theorem polynomial_literal_match_count_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialLiteralMatchCount (v 0) :=
  (Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.fstBlockFn (Cobham.sndBlockFn literal_match_state_cobham)).of_eq fun _ => rfl

 theorem polynomial_literal_match_count_mem_fp : polynomialLiteralMatchCount ∈ FP :=
  CobhamFP_subset_FP polynomial_literal_match_count_cobham

 theorem polynomial_literal_match_count_length (input : List Bool) :
    (polynomialLiteralMatchCount input).length ≤ 6*input.length+4 := by
  have hc := canonical_word_length (pairFst (pairSnd (literalMatchState input)))
  have hp := pairFst_length_le (pairSnd (literalMatchState input))
  have hp' := pairSnd_length_le (literalMatchState input)
  have hs := literal_match_clock_length input input
  change (canonicalWord (pairFst (pairSnd (literalMatchState input)))).length ≤ _
  unfold literalMatchState at hp hp' hc ⊢
  omega

#print axioms polynomial_literal_match_count_mem_fp
end IV04.Paper.Computational
