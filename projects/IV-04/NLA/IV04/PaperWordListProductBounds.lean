module

public import NLA.IV04.PaperWordListProductDefinitions
public import NLA.IV04.PaperCanonicalProduct
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem pair_projection_budget (input : List Bool) :
    (Complexity.pairFst input).length+(Complexity.pairSnd input).length ≤ input.length := by
  cases hu : Complexity.unpair? input with
  | none =>
    simp only [Complexity.pairSnd,hu,List.length_nil,Nat.add_zero]
    exact Complexity.pairFst_length_le input
  | some parsed =>
    obtain ⟨left,right⟩ := parsed
    have he : input=Complexity.pair left right := Complexity.unpair?_eq_some_iff.mp hu
    rw [he]
    simp only [Complexity.pairFst_pair,Complexity.pairSnd_pair,Complexity.pair_length]
    omega

theorem word_list_product_step_pair (rest product : List Bool) :
    wordListProductStep (Complexity.pair rest product)=
      if rest=[] then Complexity.pair rest product else
        Complexity.pair (Complexity.pairSnd rest) (canonicalWordMultiply product (Complexity.pairFst rest)) := by
  simp only [wordListProductStep,Complexity.pairFst_pair,Complexity.pairSnd_pair]
  cases rest <;> simp [Complexity.nonemptyFlag,Complexity.caseBit,Complexity.caseBit₀]

theorem word_list_product_step_shape (rest product : List Bool) :
    ∃ r p : List Bool, wordListProductStep (Complexity.pair rest product)=Complexity.pair r p ∧
      (Complexity.pair r p).length ≤ (Complexity.pair rest product).length := by
  rw [word_list_product_step_pair]
  split_ifs with he
  · exact ⟨rest,product,rfl,le_refl _⟩
  · refine ⟨_,_,rfl,?_⟩
    have hp := pair_projection_budget rest
    have hm := canonical_word_multiply_length product (Complexity.pairFst rest)
    simp only [Complexity.pair_length]
    omega

theorem word_list_product_iterate_shape (k : ℕ) (rest product : List Bool) :
    ∃ r p : List Bool, (wordListProductStep^[k]) (Complexity.pair rest product)=Complexity.pair r p ∧
      (Complexity.pair r p).length ≤ (Complexity.pair rest product).length := by
  induction k with
  | zero => exact ⟨rest,product,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨r,p,he,hl⟩ := ih
    obtain ⟨r',p',hs,hbound⟩ := word_list_product_step_shape r p
    refine ⟨r',p',?_,hbound.trans hl⟩
    rw [Function.iterate_succ_apply',he,hs]

theorem word_list_product_iterate_length (k : ℕ) (rest product : List Bool) :
    ((wordListProductStep^[k]) (Complexity.pair rest product)).length ≤
      2*rest.length+product.length+2 := by
  obtain ⟨r,p,he,hl⟩ := word_list_product_iterate_shape k rest product
  rw [he]
  simp only [Complexity.pair_length] at hl ⊢
  omega

#print axioms word_list_product_iterate_length
end IV04.Paper.Computational
