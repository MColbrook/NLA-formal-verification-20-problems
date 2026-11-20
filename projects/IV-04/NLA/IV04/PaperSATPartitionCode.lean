module

public import NLA.IV04.PaperSATPartitionCodeDefinitions
public import NLA.IV04.PaperSATDigitCorrectness
public import NLA.IV04.PaperInputEncoding
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction
open Complexity.SAT

private theorem signed_total_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : ι → ℕ) (s : κ → ℤ) :
    signedTotal (fun j => w (e.symm j)) s = signedTotal w (fun i => s (e i)) := by
  exact (Fintype.sum_equiv e (fun i => s (e i) * (w i : ℤ))
    (fun j => s j * (w (e.symm j) : ℤ)) (fun i => by simp)).symm

theorem signed_partition_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : ι → ℕ) :
    SignedPartition (fun j => w (e.symm j)) ↔ SignedPartition w := by
  constructor
  · rintro ⟨s,hs,hz⟩
    exact ⟨(fun i => s (e i)), (fun i => hs (e i)), by rw [← signed_total_reindex e w s]; exact hz⟩
  · rintro ⟨s,hs,hz⟩
    refine ⟨(fun j => s (e.symm j)), (fun j => hs (e.symm j)), ?_⟩
    rw [signed_total_reindex]
    simpa only [Equiv.symm_apply_apply] using hz

/-- The actual positive paper input with its concrete Fin indexing. -/
def actualSATPartition (φ : CNF) : IV04.Paper.IntegerPartition where
  m := satSlotCount φ+2
  nonempty := by omega
  weight := satPartitionWeight φ
  positive i := sat_partition_all_weights_positive φ ((satPartitionIndexEquiv φ).symm i)

theorem actual_sat_partition_code (φ : CNF) :
    (actualSATPartition φ).inputCode = satPartitionCode φ := rfl

theorem actual_sat_partition_iff (φ : CNF) :
    (actualSATPartition φ).HasPartition ↔ φ.Satisfiable := by
  rw [paper_partition_exact_signed]
  change SignedPartition (fun j =>
    subsetPartitionWeights (satSubsetWeights φ) (satSubsetTarget φ)
      ((satPartitionIndexEquiv φ).symm j)) ↔ φ.Satisfiable
  rw [signed_partition_reindex]
  exact (sat_satisfiable_iff_positive_partition φ).symm

/-- The actual counted binary code identifies both the dimension and every weight. -/
theorem paper_partition_input_code_injective :
    Function.Injective IV04.Paper.IntegerPartition.inputCode := by
  intro P Q h
  have hl := IV04.Paper.IntegerPartition.input_code_identifies_weights P Q h
  have hm : P.m = Q.m := by
    have hh := congrArg List.length hl
    simpa only [IV04.Paper.IntegerPartition.weight_list_length] using hh
  rcases P with ⟨m,hn,w,hw⟩
  rcases Q with ⟨n,hn',v,hv⟩
  change m = n at hm
  subst n
  have hweights : w = v := by
    apply List.ofFn_injective
    simpa only [IV04.Paper.IntegerPartition.weightList] using hl
  subst v
  rfl

theorem paper_partition_code_mem_language (P : IV04.Paper.IntegerPartition) :
    P.inputCode ∈ positivePartitionLanguage ↔ P.HasPartition := by
  constructor
  · rintro ⟨Q,h,hQ⟩
    have heq : P = Q := paper_partition_input_code_injective h
    exact heq ▸ hQ
  · intro hP
    exact ⟨P,rfl,hP⟩

def fixedNoPartition : IV04.Paper.IntegerPartition where
  m := 2
  nonempty := by decide
  weight := ![1,2]
  positive i := by fin_cases i <;> decide

theorem fixed_no_partition_rejects : ¬ fixedNoPartition.HasPartition := by
  change ¬ SignedPartition (![1,2] : Fin 2 → ℕ)
  rintro ⟨s,hs,hz⟩
  have h0 := hs 0
  have h1 := hs 1
  simp [signedTotal, Fin.sum_univ_two] at hz
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0,h1] at hz <;> norm_num at hz

private theorem binary_sat_language_iff_decoded (bits : List Bool) :
    bits ∈ Complexity.SAT.language ↔ ∃ φ : CNF, CNF.decode? bits = some φ ∧ φ.Satisfiable := by
  constructor
  · rintro ⟨φ,h,hs⟩
    subst bits
    exact ⟨φ,CNF.decode?_encode φ,hs⟩
  · rintro ⟨φ,hd,hs⟩
    exact ⟨φ,CNF.decode?_sound hd,hs⟩

/-- Correct reduction on EVERY bit input; malformed SAT codes map to [1,2]. -/
theorem actual_binary_sat_partition_reduction (bits : List Bool) :
    bits ∈ Complexity.SAT.language ↔
      binarySATPartitionReduction bits ∈ positivePartitionLanguage := by
  rw [binary_sat_language_iff_decoded]
  cases hd : CNF.decode? bits with
  | none =>
    have hcode : binarySATPartitionReduction bits = fixedNoPartition.inputCode := by
      simp [binarySATPartitionReduction, hd, fixedNoPartition,
        IV04.Paper.IntegerPartition.inputCode, IV04.Paper.IntegerPartition.weightList, countedWeightCode]
    rw [hcode,paper_partition_code_mem_language]
    simp [hd,fixed_no_partition_rejects]
  | some φ =>
    have hcode : binarySATPartitionReduction bits = (actualSATPartition φ).inputCode := by
      simp only [binarySATPartitionReduction,hd,← actual_sat_partition_code]
    rw [hcode,paper_partition_code_mem_language,actual_sat_partition_iff]
    simp [hd]

#print axioms signed_partition_reindex
#print axioms actual_sat_partition_iff
#print axioms paper_partition_input_code_injective
#print axioms paper_partition_code_mem_language
#print axioms fixed_no_partition_rejects
#print axioms actual_binary_sat_partition_reduction
end IV04.Paper.Computational.SATReduction