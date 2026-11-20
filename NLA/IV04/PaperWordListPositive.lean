module

public import NLA.IV04.PaperWordListPositiveDefinitions
public import NLA.IV04.PaperWordListProductSemantics
public import NLA.IV04.PaperSignedOrderSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem payload_product_positive (payloads : List (List Bool)) :
    0 < (payloads.map wordValue).prod ↔ ∀ w ∈ payloads, 0 < wordValue w := by
  induction payloads with
  | nil => simp
  | cons w payloads ih =>
    rw [List.map_cons,List.prod_cons]
    constructor
    · intro h a ha
      have hw : 0 < wordValue w := by
        by_contra hn
        have hz : wordValue w=0 := by omega
        rw [hz,zero_mul] at h
        omega
      have hp : 0 < (payloads.map wordValue).prod := by
        by_contra hn
        have hz : (payloads.map wordValue).prod=0 := by omega
        rw [hz,mul_zero] at h
        omega
      rcases List.mem_cons.mp ha with he | ha
      · subst a; exact hw
      · exact (ih.mp hp) a ha
    · intro h
      exact Nat.mul_pos (h w (by simp)) (ih.mpr (fun a ha => h a (by simp [ha])))

theorem positive_word_list_value (payloads : List (List Bool)) :
    polynomialPositiveWordList (payloadListCode payloads)=[decide (∀ w ∈ payloads, 0 < wordValue w)] := by
  simp only [polynomialPositiveWordList,canonical_nonempty_flag,polynomial_word_list_product_value]
  by_cases hz : (payloads.map wordValue).prod=0
  · have hn : ¬ (∀ w ∈ payloads, 0 < wordValue w) := by
      intro h
      have hp := (payload_product_positive payloads).mpr h
      omega
    simp [hz,hn,caseBit₀]
  · have hp : ∀ w ∈ payloads, 0 < wordValue w :=
      (payload_product_positive payloads).mp (by omega)
    have hd : decide (∀ w ∈ payloads, 0 < wordValue w)=true := by
      simp only [decide_eq_true_eq]
      exact hp
    simp [hz,hd,caseBit₀]

theorem nonempty_positive_word_list_value (payloads : List (List Bool)) :
    polynomialNonemptyPositiveWordList (payloadListCode payloads)=
      [decide (payloads ≠ [] ∧ ∀ w ∈ payloads, 0 < wordValue w)] := by
  rw [polynomialNonemptyPositiveWordList,positive_word_list_value]
  cases payloads with
  | nil => simp [payloadListCode,nonemptyFlag,caseBit,andBit,caseBit₀]
  | cons w payloads =>
    have hp : (w :: payloads ≠ [] ∧ ∀ a ∈ w :: payloads, 0 < wordValue a) ↔
        (∀ a ∈ w :: payloads, 0 < wordValue a) :=
      ⟨And.right,fun h => ⟨by simp,h⟩⟩
    simp only [hp]
    have hn : payloadListCode (w :: payloads) ≠ [] := by
      intro he
      have hl := payload_list_count_length (w :: payloads)
      rw [he] at hl
      simp at hl
    cases hc : payloadListCode (w :: payloads) with
    | nil => exact (hn hc).elim
    | cons b bits =>
      cases b <;> simp only [List.cons_ne_nil,not_false_eq_true,true_and,nonemptyFlag,caseBit,
        andBit,caseBit₀,Bool.cond_true,Bool.cond_false] <;>
        cases q : decide (∀ a ∈ w :: payloads, 0 < wordValue a) <;>
        simp only [q,Bool.cond_true,Bool.cond_false]

theorem positive_word_list_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPositiveWordList (v 0) := by
  have hp := Cobham.sndBlockFn word_list_product_state_cobham
  have hn := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hp)
  exact (Cobham.iteFn hn (Cobham.const [true]) (Cobham.const [false])).of_eq fun _ => rfl

theorem positive_word_list_mem_fp : polynomialPositiveWordList ∈ FP :=
  CobhamFP_subset_FP positive_word_list_cobham

theorem nonempty_positive_word_list_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialNonemptyPositiveWordList (v 0) :=
  (Cobham.andFn (Cobham.nonemptyFn (Cobham.proj (0 : Fin 1))) positive_word_list_cobham).of_eq fun _ => rfl

theorem nonempty_positive_word_list_mem_fp : polynomialNonemptyPositiveWordList ∈ FP :=
  CobhamFP_subset_FP nonempty_positive_word_list_cobham

#print axioms positive_word_list_mem_fp
end IV04.Paper.Computational
