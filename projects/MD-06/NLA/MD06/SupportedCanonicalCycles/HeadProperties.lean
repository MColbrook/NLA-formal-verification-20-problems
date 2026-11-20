module

public import NLA.MD06.SupportedCanonicalCycles.HeadDefinitions
public import NLA.MD06.SupportedCanonicalCycles.SupportProperties

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06SupportedCanonicalCycles
open Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

theorem actual_cycle_head_remaining_card {n ell : ℕ} (S : Finset (Fin n))
    (C : SupportedCanonicalCycle S ell) :
    (S\VertexSupport C.val.val).card=S.card-ell := by
  rw [Finset.card_sdiff_of_subset C.property,actual_supported_cycle_vertex_card S C]

theorem actual_cycle_weight_zero (L : Fin 0→ℕ) : CycleWeight L=0 := by
  simp [CycleWeight]

theorem actual_cycle_weight_succ {q : ℕ} (L : Fin (q+1)→ℕ) :
    CycleWeight L=L 0+CycleWeight (Fin.tail L) := by
  simp only [CycleWeight,Fin.sum_univ_succ,Fin.tail]

theorem actual_cycle_factor_zero (L : Fin 0→ℕ) : CycleSymmetryFactor L=1 := by
  simp [CycleSymmetryFactor]

theorem actual_cycle_factor_succ {q : ℕ} (L : Fin (q+1)→ℕ) :
    CycleSymmetryFactor L=(2*L 0)*CycleSymmetryFactor (Fin.tail L) := by
  simp only [CycleSymmetryFactor,Fin.prod_univ_succ,Fin.tail]

#print axioms actual_cycle_head_remaining_card
#print axioms actual_cycle_weight_zero
#print axioms actual_cycle_weight_succ
#print axioms actual_cycle_factor_zero
#print axioms actual_cycle_factor_succ
end Reference.MD06SupportedCanonicalCycles
