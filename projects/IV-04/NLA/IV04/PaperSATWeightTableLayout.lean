module

public import NLA.IV04.PaperSATWeightTableSemantics
public import NLA.IV04.PaperSubsetPartitionBuilderSemantics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational
open Complexity SATReduction
 theorem sat_table_ofFn_prod {α : Type*} {m n : ℕ} (f : Fin m × Fin n → α) :
    List.ofFn (fun i : Fin (m*n) => f (finProdFinEquiv.symm i))=
      (List.ofFn (fun i : Fin m => List.ofFn (fun j : Fin n => f (i,j)))).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  apply congrArg f
  apply (finProdFinEquiv : Fin m × Fin n ≃ Fin (m*n)).injective
  rw [Equiv.apply_symm_apply]
  apply Fin.ext
  change i.val*n+j.val=j.val+n*i.val
  ac_rfl
 theorem sat_table_subset_layout (formula : SAT.CNF) :
    List.ofFn (fun i : Fin (satSlotCount formula) =>
      (satSubsetWeights formula ((satSlotFinEquiv formula).symm i)).bits)=
      (List.ofFn (fun v : Fin (satVariables formula) => List.ofFn (fun b : Fin 2 =>
        (satSubsetWeights formula (Sum.inl (v,boolFinTwo.symm b))).bits))).flatten ++
      (List.ofFn (fun j : Fin formula.length => List.ofFn (fun k : Fin (satClauseTarget formula-1) =>
        (satSubsetWeights formula (Sum.inr (j,k))).bits))).flatten := by
  have hf : (fun i : Fin (satSlotCount formula) =>
      (satSubsetWeights formula ((satSlotFinEquiv formula).symm i)).bits)=
      Fin.append
        (fun i : Fin (satVariables formula*2) =>
          (satSubsetWeights formula (Sum.inl ((finProdFinEquiv.symm i).1,
            boolFinTwo.symm (finProdFinEquiv.symm i).2))).bits)
        (fun i : Fin (formula.length*(satClauseTarget formula-1)) =>
          (satSubsetWeights formula (Sum.inr (finProdFinEquiv.symm i))).bits) := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro v
      change (satSubsetWeights formula
        ((Equiv.sumCongr
          ((Equiv.prodCongr (Equiv.refl (Fin (satVariables formula))) boolFinTwo).trans finProdFinEquiv)
          finProdFinEquiv).symm
          (finSumFinEquiv.symm (Fin.castAdd (formula.length*(satClauseTarget formula-1)) v)))).bits=_
      rw [finSumFinEquiv_symm_apply_castAdd]
      simp [Fin.append, Equiv.sumCongr, Equiv.prodCongr]
    · intro j
      change (satSubsetWeights formula
        ((Equiv.sumCongr
          ((Equiv.prodCongr (Equiv.refl (Fin (satVariables formula))) boolFinTwo).trans finProdFinEquiv)
          finProdFinEquiv).symm
          (finSumFinEquiv.symm (Fin.natAdd (satVariables formula*2) j)))).bits=_
      rw [finSumFinEquiv_symm_apply_natAdd]
      simp [Fin.append, Equiv.sumCongr, Equiv.prodCongr]
  dsimp only [satSlotCount] at hf ⊢
  rw [hf,List.ofFn_fin_append]
  rw [sat_table_ofFn_prod (fun p : Fin (satVariables formula) × Fin 2 =>
      (satSubsetWeights formula (Sum.inl (p.1,boolFinTwo.symm p.2))).bits),
    sat_table_ofFn_prod (fun p : Fin formula.length × Fin (satClauseTarget formula-1) =>
      (satSubsetWeights formula (Sum.inr p)).bits)]
 theorem polynomial_sat_reversed_weights_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATReversedWeights bits=payloadListCode
      (List.ofFn (fun i : Fin (satSlotCount formula) =>
        (satSubsetWeights formula ((satSlotFinEquiv formula).symm i)).bits)).reverse := by
  have hv := sat_variables_le_decoded_input bits formula h
  have hm : formula.length ≤ bits.length+1 := by
    have hc := sat_clauses_le_input_length formula
    rw [← SAT.CNF.decode?_sound h] at hc
    omega
  have hl := sat_table_map_chunks_exact polynomialSATLiteralChunk bits bits (satVariables formula)
    (fun v => List.ofFn (fun b : Fin 2 =>
      (satSubsetWeights formula (Sum.inl (v,boolFinTwo.symm b))).bits)) hv
    (fun v => polynomial_sat_literal_chunk_exact bits formula v h)
  have hs := sat_table_map_chunks_exact polynomialSATSlackChunk bits bits formula.length
    (fun j => List.ofFn (fun k : Fin (satClauseTarget formula-1) =>
      (satSubsetWeights formula (Sum.inr (j,k))).bits)) hm
    (fun j => polynomial_sat_slack_chunk_exact bits formula j h)
  rw [sat_table_subset_layout]
  simp only [polynomialSATReversedWeights,polynomial_sat_table_metadata_exact bits formula h,
    pairFst_pair,pairSnd_pair]
  rw [hs,hl,← literal_digits_payload_append,← List.reverse_append]
 theorem polynomial_sat_weight_table_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATWeightTable bits=payloadListCode
      (List.ofFn (fun i : Fin (satSlotCount formula) =>
        (satSubsetWeights formula ((satSlotFinEquiv formula).symm i)).bits)) := by
  rw [polynomialSATWeightTable,polynomial_sat_reversed_weights_exact bits formula h,
    payload_reverse_code,List.reverse_reverse]
 theorem polynomial_sat_subset_input_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATSubsetInput bits=subsetPartitionBuilderInput (satSlotCount formula)
      (fun i => satSubsetWeights formula ((satSlotFinEquiv formula).symm i)) (satSubsetTarget formula) := by
  simp only [polynomialSATSubsetInput,polynomial_sat_table_count_exact bits formula h,
    polynomial_sat_target_weight_exact bits formula h,polynomial_sat_weight_table_exact bits formula h,
    subsetPartitionBuilderInput,List.map_ofFn,Function.comp_def]
 theorem sat_table_builder_weights_exact (formula : SAT.CNF) :
    subsetPartitionBuilderWeights
      (fun i : Fin (satSlotCount formula) => satSubsetWeights formula ((satSlotFinEquiv formula).symm i))
      (satSubsetTarget formula)=satPartitionWeight formula := by
  have hsum : (∑ i : Fin (satSlotCount formula),
      satSubsetWeights formula ((satSlotFinEquiv formula).symm i))=
      ∑ i : SATSlot formula, satSubsetWeights formula i := by
    exact (Fintype.sum_equiv (satSlotFinEquiv formula) (satSubsetWeights formula)
      (fun i => satSubsetWeights formula ((satSlotFinEquiv formula).symm i)) (fun _ => by simp)).symm
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j;simp [subsetPartitionBuilderWeights,satPartitionWeight,satPartitionIndexEquiv,
      subsetPartitionWeights]
  · intro b;fin_cases b <;> simp [subsetPartitionBuilderWeights,satPartitionWeight,
      satPartitionIndexEquiv,subsetPartitionWeights,boolFinTwo,hsum]
 theorem polynomial_sat_partition_code_exact (bits : List Bool) :
    polynomialSATPartitionCode bits=binarySATPartitionReduction bits := by
  cases hd : SAT.CNF.decode? bits with
  | none =>
    rw [polynomialSATPartitionCode,polynomial_sat_cnf_parse_reject bits hd]
    simp [caseBit₀,binarySATPartitionReduction,hd]
  | some formula =>
    rw [polynomialSATPartitionCode,polynomial_sat_cnf_parse_exact bits formula hd,pairFst_pair]
    simp only [caseBit₀]
    rw [polynomial_sat_subset_input_exact bits formula hd,polynomial_subset_partition_code_exact,
      sat_table_builder_weights_exact]
    simp [binarySATPartitionReduction,hd,satPartitionCode]
 theorem sat_partition_code_actual_polytime : polynomialSATPartitionCode ∈ FP ∧
    (∀ bits, polynomialSATPartitionCode bits=binarySATPartitionReduction bits) ∧
    (∀ bits, bits ∈ Complexity.SAT.language ↔
      polynomialSATPartitionCode bits ∈ positivePartitionLanguage) := by
  refine ⟨polynomial_sat_partition_code_mem_fp,polynomial_sat_partition_code_exact,?_⟩
  intro bits
  rw [polynomial_sat_partition_code_exact]
  exact actual_binary_sat_partition_reduction bits
#print axioms sat_table_subset_layout
#print axioms polynomial_sat_weight_table_exact
#print axioms polynomial_sat_partition_code_exact
#print axioms sat_partition_code_actual_polytime
end IV04.Paper.Computational
