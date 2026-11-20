module

/- Kernel checks for explicit finite ascending scan enumeration and lookup. -/
public import NLA.TR04.OrderedTensorSolver.IndexDefinitions
public import Mathlib.Data.List.Sort
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.OrderedIndex

theorem indexList_ascending {m : ℕ} (p : Fin m → Prop) [DecidablePred p] :
    (indexList p).SortedLT := ((List.sortedLT_finRange m).pairwise.filter _).sortedLT

#print axioms mem_indexList
#print axioms nodup_indexList
#print axioms indexList_length
#print axioms indexEnum_inverse_lookup
#print axioms indexEnum_forward_lookup
#print axioms indexList_ascending
end Reference.OrderedIndex
