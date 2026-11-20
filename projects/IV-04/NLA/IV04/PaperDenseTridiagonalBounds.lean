module

public import NLA.IV04.PaperDenseTridiagonalDefinitions
public import NLA.IV04.PaperTridiagonalCell
public import NLA.IV04.PaperCountedMachineStep
public import NLA.IV04.PaperWordListProductBounds
public import NLA.IV04.PaperSignedWordBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem dense_support_pack_length (d c i j f b : List Bool) :
    (denseSupportPack d c i j f b).length=
      2*d.length+2*c.length+2*i.length+2*j.length+2*f.length+b.length+10 := by
  simp [denseSupportPack,pair_length];omega

theorem dense_and_flag_length (a b : List Bool) : (andBit a b).length ≤ 1 := by
  unfold andBit
  exact case_bit_zero_property (P:=fun bits => bits.length ≤ 1) a _ _
    (case_bit_zero_property (P:=fun bits => bits.length ≤ 1) b _ _ (by decide) (by decide)) (by decide)

theorem dense_increment_word_length (word : List Bool) :
    (canonicalWord (polynomialWordAdd word [true])).length ≤ word.length+2 := by
  have h := canonical_word_length (polynomialWordAdd word [true])
  rw [polynomial_word_add_length] at h
  simpa using h

theorem dense_support_step_pack (d c i j f b : List Bool) :
    denseSupportStep (denseSupportPack d c i j f b)=denseSupportTransition d c i j f b := by
  simp only [denseSupportStep,denseSupportDimension,denseSupportCount,denseSupportRow,
    denseSupportColumn,denseSupportFields,denseSupportFlag,denseSupportPack,pairFst_pair,pairSnd_pair]

theorem dense_support_step_shape (d c i j f b : List Bool) :
    ∃ d' c' i' j' f' b' : List Bool,
      denseSupportStep (denseSupportPack d c i j f b)=denseSupportPack d' c' i' j' f' b' ∧
      (denseSupportPack d' c' i' j' f' b').length ≤ (denseSupportPack d c i j f b).length+9 := by
  rw [dense_support_step_pack]
  unfold denseSupportTransition
  dsimp only
  apply case_bit_zero_property (P:=fun output => ∃ d' c' i' j' f' b' : List Bool,
    output=denseSupportPack d' c' i' j' f' b' ∧
    (denseSupportPack d' c' i' j' f' b').length ≤ (denseSupportPack d c i j f b).length+9)
  · refine ⟨_,_,_,_,_,_,rfl,?_⟩
    have hc := decrement_count_length c
    have hi := case_bit_zero_property (P:=fun bits => bits.length ≤ i.length+2)
      (polynomialWordLe d (canonicalWord (polynomialWordAdd j [true])))
      (canonicalWord (polynomialWordAdd i [true])) i
      (dense_increment_word_length i) (show i.length ≤ i.length+2 by omega)
    have hj := case_bit_zero_property (P:=fun bits => bits.length ≤ j.length+2)
      (polynomialWordLe d (canonicalWord (polynomialWordAdd j [true])))
      [] (canonicalWord (polynomialWordAdd j [true]))
      (show ([] : List Bool).length ≤ j.length+2 by simp)
      (dense_increment_word_length j)
    have hf := pair_projection_budget f
    have hf' := pair_projection_budget (pairSnd f)
    have hb := dense_and_flag_length b
      (andBit (andBit (nonemptyFlag f) (nonemptyFlag (pairSnd f)))
        (tridiagonalEndpointFlag i j (pairFst f) (pairFst (pairSnd f))))
    simp only [dense_support_pack_length]
    omega
  · refine ⟨d,c,i,j,f,b,rfl,?_⟩;omega

theorem dense_support_iterate_shape (k : ℕ) (d c i j f b : List Bool) :
    ∃ d' c' i' j' f' b' : List Bool,
      (denseSupportStep^[k]) (denseSupportPack d c i j f b)=denseSupportPack d' c' i' j' f' b' ∧
      (denseSupportPack d' c' i' j' f' b').length ≤ (denseSupportPack d c i j f b).length+9*k := by
  induction k with
  | zero => exact ⟨d,c,i,j,f,b,rfl,by simp⟩
  | succ k ih =>
    obtain ⟨d',c',i',j',f',b',he,hl⟩ := ih
    obtain ⟨d'',c'',i'',j'',f'',b'',hs,hbound⟩ := dense_support_step_shape d' c' i' j' f' b'
    refine ⟨d'',c'',i'',j'',f'',b'',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

theorem dense_support_initial_length (input : List Bool) :
    (denseSupportInitial input).length ≤ 6*input.length+11 := by
  have hd := canonical_word_length (pairFst input)
  have hc := canonical_word_multiply_length (canonicalWord (pairFst input)) (canonicalWord (pairFst input))
  have hp := pair_projection_budget input
  simp only [denseSupportInitial,dense_support_pack_length,List.length_nil,List.length_cons] at *
  omega

theorem dense_support_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((denseSupportStep^[k]) (denseSupportInitial input)).length ≤ 6*input.length+11+9*k := by
  obtain ⟨d,c,i,j,f,b,he,hl⟩ := dense_support_iterate_shape k
    (canonicalWord (pairFst input)) (canonicalWordMultiply (canonicalWord (pairFst input)) (canonicalWord (pairFst input)))
    [] [] (pairSnd input) [true]
  rw [←he] at hl
  change ((denseSupportStep^[k]) (denseSupportInitial input)).length ≤
    (denseSupportInitial input).length+9*k at hl
  exact hl.trans (by have hi := dense_support_initial_length input;omega)

#print axioms dense_support_initial_iterate_length
end IV04.Paper.Computational
