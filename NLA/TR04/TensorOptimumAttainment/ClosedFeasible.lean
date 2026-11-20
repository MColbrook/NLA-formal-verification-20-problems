module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual finite tensor cut-rank feasible sets are nonempty and closed. -/
public import NLA.TR04.TensorOptimumAttainment.ClosedRank

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.TensorOptimumAttainment
noncomputable section
open Reference.RecursiveTensorCompletion
open scoped Matrix

theorem continuous_merge {m n : ℕ} {ns : List ℕ} :
    Continuous (merge : Tensor m (n::ns) → Tensor (rowCount m n) ns) := by
  unfold merge
  exact continuous_pi fun i => continuous_pi fun j =>
    (continuous_apply (((rowEquiv m n).symm i).2,j)).comp
      (continuous_apply ((rowEquiv m n).symm i).1)

theorem actual_tensor_feasible_isClosed (m : ℕ) (ns rs : List ℕ) :
    IsClosed (feasibleSet m ns rs) := by
  induction ns generalizing m rs with
  | nil =>
    by_cases h : rs=[]
    · simp [feasibleSet,feasible,h]
    · simp [feasibleSet,feasible,h]
  | cons n ns ih =>
    cases rs with
    | nil => simp [feasibleSet,feasible]
    | cons r rs =>
      have he : feasibleSet m (n::ns) (r::rs) =
          {A : Tensor m (n::ns) | A.rank≤r} ∩ merge ⁻¹' feasibleSet (rowCount m n) ns rs := by
        ext A
        simp only [feasibleSet,feasible,Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage]
      rw [he]
      exact (actual_matrix_rank_bound_isClosed r).inter ((ih _ _).preimage continuous_merge)

theorem actual_zero_tensor_feasible (m : ℕ) (ns rs : List ℕ) (hlen : rs.length=ns.length) :
    feasible m ns (0 : Tensor m ns) rs := by
  induction ns generalizing m rs with
  | nil => simpa only [feasible] using List.length_eq_zero_iff.mp hlen
  | cons n ns ih =>
    cases rs with
    | nil => simp at hlen
    | cons r rs =>
      have hnext : rs.length=ns.length := by simpa using hlen
      have hzero : merge (0 : Tensor m (n::ns))=0 := by ext i j;rfl
      simp only [feasible,hzero,Matrix.rank_zero]
      exact ⟨Nat.zero_le r,ih _ _ hnext⟩

#print axioms actual_tensor_feasible_isClosed
#print axioms actual_zero_tensor_feasible
end
end Reference.TensorOptimumAttainment
