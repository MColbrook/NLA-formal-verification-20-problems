module

public import NLA.IV04.PaperCanonicalWordDefinitions
public import NLA.IV04.PaperWordAdderPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem canonical_word_length (bits : List Bool) :
    (canonicalWord bits).length ≤ bits.length := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases b <;> simp only [canonicalWord,List.length_cons]
    · split_ifs <;> simp_all <;> omega
    · omega

theorem canonical_word_value (bits : List Bool) :
    wordValue (canonicalWord bits)=wordValue bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases b <;> simp only [canonicalWord,wordValue,bitValue,Bool.false_eq_true,ite_false,ite_true]
    · split_ifs with h
      · rw [h] at ih
        simp only [wordValue] at ih ⊢
        omega
      · simp [wordValue,bitValue,ih]
    · rw [ih]

theorem canonical_word_eq_bits (bits : List Bool) :
    canonicalWord bits=(wordValue bits).bits := by
  induction bits with
  | nil => simp [canonicalWord,wordValue]
  | cons b bits ih =>
    cases b
    · by_cases hz : wordValue bits=0
      · simp [canonicalWord,ih,hz,wordValue,bitValue]
      · have hb := Nat.bits_append_bit (wordValue bits) false (by intro h; exact (hz h).elim)
        have hn : (wordValue bits).bits ≠ [] := by
          intro h
          have hd : ((wordValue bits).bits).foldr Nat.bit 0 = wordValue bits := by
            induction wordValue bits using Nat.binaryRec' with
            | zero => simp
            | bit b n hn ih => simp [Nat.bits_append_bit n b hn,ih]
          rw [h] at hd
          exact hz hd.symm
        simpa [canonicalWord,ih,hn,wordValue,bitValue,Nat.bit] using hb.symm
    · have hb := Nat.bits_append_bit (wordValue bits) true (fun _ => rfl)
      simpa [canonicalWord,ih,wordValue,bitValue,Nat.bit] using hb.symm

theorem canonical_word_idempotent (bits : List Bool) :
    canonicalWord (canonicalWord bits)=canonicalWord bits := by
  rw [canonical_word_eq_bits,canonical_word_value,←canonical_word_eq_bits]

theorem canonical_word_cobham :
    Cobham fun v : Fin 1 → List Bool => canonicalWord (v 0) := by
  let base : (Fin 0 → List Bool) → List Bool := fun _ => []
  let zero : (Fin 2 → List Bool) → List Bool :=
    fun v => if v 1=[] then [] else false :: v 1
  let one : (Fin 2 → List Bool) → List Bool := fun v => true :: v 1
  have hg : Cobham base := .const []
  have ht : Cobham fun v : Fin 2 → List Bool => false :: v 1 :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hz : Cobham zero :=
    (Cobham.iteFn (Cobham.nonemptyFn (.proj 1)) ht (.const [])).of_eq fun v => by
      cases h : v 1 <;> simp [zero,h,caseBit₀,nonemptyFlag,caseBit]
  have ho : Cobham one :=
    (Cobham.comp (.bit true) fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hrec : ∀ (bits : List Bool) (v : Fin 0 → List Bool),
      recNotation base zero one bits v=canonicalWord bits := by
    intro bits v
    induction bits with
    | nil => rfl
    | cons b bits ih =>
      cases b <;> simp [recNotation,base,zero,one,canonicalWord,ih]
  refine (Cobham.boundedRec hg hz ho (Cobham.proj 0) ?_).of_eq fun v => ?_
  · intro bits v
    rw [hrec]
    exact canonical_word_length bits
  · exact hrec (v 0) (Fin.tail v)

theorem canonical_word_mem_fp : canonicalWord ∈ FP :=
  CobhamFP_subset_FP canonical_word_cobham

theorem canonical_word_code_cobham :
    Cobham fun v : Fin 1 → List Bool => canonicalWordCode (v 0) := by
  have hh := Cobham.comp₂ Cobham.smash canonical_word_cobham (Cobham.const [true])
  have ht : Cobham fun v : Fin 1 → List Bool => false :: canonicalWord (v 0) :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => canonical_word_cobham).of_eq fun _ => rfl
  exact (Cobham.appendFn hh ht).of_eq fun v => by simp [canonicalWordCode,Complexity.smash]

theorem canonical_word_code_mem_fp : canonicalWordCode ∈ FP :=
  CobhamFP_subset_FP canonical_word_code_cobham

theorem canonical_word_code_length (bits : List Bool) :
    (canonicalWordCode bits).length=2*(wordValue bits).size+1 := by
  simp [canonicalWordCode,canonical_word_eq_bits,←Nat.size_eq_bits_len]
  omega

theorem canonical_word_code_length_bound (bits : List Bool) :
    (canonicalWordCode bits).length ≤ 2*bits.length+1 := by
  have h := canonical_word_length bits
  simp only [canonicalWordCode,List.length_append,List.length_replicate,List.length_cons]
  omega

#print axioms canonical_word_code_mem_fp
end IV04.Paper.Computational
