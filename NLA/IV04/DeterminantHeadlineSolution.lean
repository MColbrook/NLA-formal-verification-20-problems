module

public import NLA.IV04.PaperDeterminantHeadline

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction

#print axioms actual_sat_matrix_packet_regular

#print axioms actual_sat_output_query_packet_regular

#print axioms actual_binary_sat_regular_determinant_reduction

#print axioms actual_binary_sat_regular_determinant_map_reduction

#print axioms actual_regular_unit_determinant_np_hard

#print axioms regular_unit_exact_determinant_range_output_np_hard

#print axioms actual_paper_iv_det
end IV04.Paper.Computational
