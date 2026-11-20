module

public import NLA.IV04.PaperInputEncoding
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Matrix
namespace IV04.Paper

theorem verified_read_naturals_codes (weights : List ℕ) (tail : List Bool) :
    readNaturals weights.length (weights.flatMap naturalCode ++ tail) = some (weights,tail) := by
  exact read_naturals_codes weights tail

namespace IntegerPartition
theorem verified_weight_list_length (P : IntegerPartition) : P.weightList.length = P.m := by
  exact weight_list_length P
end IntegerPartition


namespace IntegerPartition
theorem verified_weight_list_positive (P : IntegerPartition) :
    ∀ w ∈ P.weightList, 0 < w := by
  exact weight_list_positive P
end IntegerPartition


namespace IntegerPartition
theorem verified_read_actual_input (P : IntegerPartition) (tail : List Bool) :
    readIntegerWeights (P.inputCode ++ tail) = some (P.weightList,tail) := by
  exact read_actual_input P tail
end IntegerPartition


namespace IntegerPartition
theorem verified_input_code_identifies_weights (P Q : IntegerPartition) (h : P.inputCode=Q.inputCode) :
    P.weightList=Q.weightList := by
  exact input_code_identifies_weights P Q h
end IntegerPartition


namespace IntegerPartition
theorem verified_input_code_length (P : IntegerPartition) :
    P.inputCode.length = 2*P.m.size+1+2*P.inputBits+P.m := by
  exact input_code_length P
end IntegerPartition


namespace IntegerPartition
theorem verified_input_payload_le_code_length (P : IntegerPartition) :
    P.inputBits ≤ P.inputCode.length := by
  exact input_payload_le_code_length P
end IntegerPartition


namespace IntegerPartition
theorem verified_matrix_box_size_in_actual_input (P : IntegerPartition) :
    P.matrixBoxCode.length ≤
      (2*(4*P.inputCode.length)^2+1)*(16*P.inputCode.length+35)+8*P.inputCode.length+1 := by
  exact matrix_box_size_in_actual_input P
end IntegerPartition


#print axioms IV04.Paper.verified_read_naturals_codes
#print axioms IV04.Paper.IntegerPartition.verified_weight_list_length
#print axioms IV04.Paper.IntegerPartition.verified_weight_list_positive
#print axioms IV04.Paper.IntegerPartition.verified_read_actual_input
#print axioms IV04.Paper.IntegerPartition.verified_input_code_identifies_weights
#print axioms IV04.Paper.IntegerPartition.verified_input_code_length
#print axioms IV04.Paper.IntegerPartition.verified_input_payload_le_code_length
#print axioms IV04.Paper.IntegerPartition.verified_matrix_box_size_in_actual_input
end IV04.Paper
