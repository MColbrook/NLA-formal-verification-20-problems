module

public import NLA.IV04.PaperInputEncodingDefinitions
public import NLA.IV04.PaperEncodingSize

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper

theorem read_naturals_codes (weights : List ℕ) (tail : List Bool) :
    readNaturals weights.length (weights.flatMap naturalCode ++ tail) = some (weights,tail) := by
  induction weights with
  | nil => rfl
  | cons value weights ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,readNaturals,
      read_natural_code,bind,Option.bind_some,ih,Option.pure_def]

namespace IntegerPartition

theorem weight_list_length (P : IntegerPartition) : P.weightList.length = P.m := by
  simp [weightList]

theorem weight_list_positive (P : IntegerPartition) :
    ∀ w ∈ P.weightList, 0 < w := by
  intro w hw
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
  exact P.positive i

theorem read_actual_input (P : IntegerPartition) (tail : List Bool) :
    readIntegerWeights (P.inputCode ++ tail) = some (P.weightList,tail) := by
  simp only [inputCode,List.append_assoc,readIntegerWeights,read_natural_code,
    bind,Option.bind_some]
  rw [← weight_list_length P,read_naturals_codes]

theorem input_code_identifies_weights (P Q : IntegerPartition) (h : P.inputCode=Q.inputCode) :
    P.weightList=Q.weightList := by
  have hp := read_actual_input P []
  have hq := read_actual_input Q []
  rw [h,hq] at hp
  exact (congrArg Prod.fst (Option.some.inj hp)).symm

theorem input_code_length (P : IntegerPartition) :
    P.inputCode.length = 2*P.m.size+1+2*P.inputBits+P.m := by
  simp only [inputCode,List.length_append,natural_code_length,List.length_flatMap,
    weightList,List.map_ofFn,List.sum_ofFn,natural_code_length,inputBits,Function.comp_apply]
  rw [Finset.sum_add_distrib,Finset.mul_sum]
  simp
  ring

theorem input_payload_le_code_length (P : IntegerPartition) :
    P.inputBits ≤ P.inputCode.length := by
  rw [input_code_length]
  omega

theorem matrix_box_size_in_actual_input (P : IntegerPartition) :
    P.matrixBoxCode.length ≤
      (2*(4*P.inputCode.length)^2+1)*(16*P.inputCode.length+35)+8*P.inputCode.length+1 := by
  have hL := input_payload_le_code_length P
  have hpow : (4*P.inputBits)^2 ≤ (4*P.inputCode.length)^2 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left 4 hL) 2
  have hp := Nat.mul_le_mul
    (show 2*(4*P.inputBits)^2+1 ≤ 2*(4*P.inputCode.length)^2+1 by omega)
    (show 16*P.inputBits+35 ≤ 16*P.inputCode.length+35 by omega)
  exact (matrix_box_code_polynomial_size P).trans (by omega)

end IntegerPartition
end IV04.Paper
