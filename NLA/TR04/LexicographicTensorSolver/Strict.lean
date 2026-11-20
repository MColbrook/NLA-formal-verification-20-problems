module

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- All mathematical branches of the actual ordered candidate-selection solver. -/
public import NLA.TR04.LexicographicTensorSolver.FullBound

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexOrderedTensorSolver
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary
open scoped Matrix

theorem actual_tail_le_feasible_error {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hY : feasible m (n::ns) Y (r::rs)) :
    singularTailSq (denseTensor A) r ≤ error A Y := by
  have hFirst : Y.rank ≤ r := by simp only [feasible] at hY;exact hY.1
  have hY0 : (denseTensor Y).rank ≤ r := by rw [denseTensor_rank];exact hFirst
  have h := singularTail_le_lowRankError (denseTensor A) (denseTensor Y) r hY0
  rw [← denseTensor_sub,denseTensor_frobenius] at h
  exact h

theorem actual_first_cut_rank_le_tail_zero {m : ℕ} {ns : List ℕ}
    (A : Tensor m ns) (r : ℕ) (hRank : (denseTensor A).rank ≤ r) :
    singularTailSq (denseTensor A) r=0 := by
  have h := (svdFrame_correct A r).2 A (by rw [denseTensor_rank] at hRank;exact hRank)
  rw [leadingFrame_projection_error] at h
  have hn : 0 ≤ singularTailSq (denseTensor A) r := by
    rw [← leadingFrame_projection_error]
    exact tensorFrobeniusSq_nonneg _
  exact le_antisymm (by simpa [tensorFrobeniusSq] using h) hn

theorem solver_strict_if_first_tail_smaller {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hY : feasible m (n::ns) Y (r::rs)) (hgap : singularTailSq (denseTensor A) r<error A Y) :
    error A (solver A r rs)<((ns.length : ℝ)+1)*error A Y := by
  have h := (solver_feasible_and_bound A r rs hlen hr).2 Y hY
  nlinarith

theorem solver_strict_if_first_rank_le {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hY : feasible m (n::ns) Y (r::rs)) (hRank : (denseTensor A).rank ≤ r) (hpositive : 0<error A Y) :
    error A (solver A r rs)<((ns.length : ℝ)+1)*error A Y := by
  apply solver_strict_if_first_tail_smaller A Y r rs hlen hr hY
  rw [actual_first_cut_rank_le_tail_zero A r hRank]
  exact hpositive

theorem solver_strict_against_every_positive_feasible_comparator {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hY : feasible m (n::ns) Y (r::rs)) (hpositive : 0<error A Y) :
    error A (solver A r rs)<((ns.length : ℝ)+1)*error A Y := by
  classical
  have hlo := actual_tail_le_feasible_error A Y r rs hY
  by_cases hgap : singularTailSq (denseTensor A) r<error A Y
  · exact solver_strict_if_first_tail_smaller A Y r rs hlen hr hY hgap
  have hequal : tensorFrobeniusSq (A-Y)=singularTailSq (denseTensor A) r :=
    le_antisymm (le_of_not_gt hgap) hlo
  have hrank : r<(denseTensor A).rank := by
    by_contra hnot
    have hz := actual_first_cut_rank_le_tail_zero A r (le_of_not_gt hnot)
    rw [← hequal] at hz
    exact (ne_of_gt hpositive) hz
  have hp := actual_boundary_parameters (denseTensor A) r hr hrank
  have ht : 0<tensorBoundaryCount A r := lt_of_lt_of_le hp.1 hp.2.1
  have hRank : ¬(denseTensor A).rank ≤ r := not_le_of_gt hrank
  by_cases hfull : tensorRetainedBoundary A r=tensorBoundaryCount A r
  · let j : Fin (tensorBoundaryCount A r) := ⟨0,ht⟩
    have hbound := (every_full_tie_completion_bound A Y r rs hlen hr hrank hY hequal hfull j).2
    have hmem : cyclicCompletion A r rs j ∈ candidates A r rs := by
      simp only [candidates,if_neg hRank,dif_pos ht,if_pos hfull,List.mem_singleton]
      rfl
    have hs := (solver_dominates A r rs _ hmem).trans hbound
    have hn : (0 : ℝ)<(ns.length : ℝ) := by exact_mod_cast hns
    have hm := mul_pos hn hpositive
    nlinarith
  · have hpartial : tensorRetainedBoundary A r<tensorBoundaryCount A r :=
      lt_of_le_of_ne hp.2.1 hfull
    obtain ⟨j,hj,hstrict⟩ := actual_partial_tie_strict_completion A Y r rs hlen hr hrank hY
      hequal hpositive hns hpartial
    have hmem : cyclicCompletion A r rs j ∈ candidates A r rs := by
      simp only [candidates,if_neg hRank,dif_pos ht,if_neg hfull]
      exact List.mem_ofFn.mpr ⟨j,rfl⟩
    exact (solver_dominates A r rs _ hmem).trans_lt hstrict

theorem solver_recovers_any_zero_error_feasible_comparator {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hY : feasible m (n::ns) Y (r::rs)) (hzero : error A Y=0) : solver A r rs=A := by
  have hZ : denseTensor (A-Y)=0 := (frobeniusSq_eq_zero_iff _).mp (by rw [denseTensor_frobenius];exact hzero)
  have h := congrArg (fun M => M.submatrix id (concreteLayout (n::ns))) hZ
  have hAY : A-Y=0 := by simpa [denseTensor,Matrix.submatrix_submatrix] using h
  have he : A=Y := sub_eq_zero.mp hAY
  subst Y
  exact solver_exact_for_feasible_input A r rs hlen hr hY

theorem actual_solver_mathematical_guarantee {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hm : 0<m) :
    feasible m (n::ns) (solver A r rs) (r::rs) ∧ (candidates A r rs).length ≤ m ∧
      (∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) → 0<error A Y →
        error A (solver A r rs)<((ns.length : ℝ)+1)*error A Y) ∧
      (∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) → error A Y=0 → solver A r rs=A) := by
  exact ⟨(solver_feasible_and_bound A r rs hlen hr).1,actual_completion_count_le_first_mode A r rs hm,
    fun Y hY hp => solver_strict_against_every_positive_feasible_comparator A Y r rs hlen hr hns hY hp,
    fun Y hY hz => solver_recovers_any_zero_error_feasible_comparator A Y r rs hlen hr hY hz⟩

#print axioms solver_strict_if_first_rank_le
#print axioms solver_strict_against_every_positive_feasible_comparator
#print axioms solver_recovers_any_zero_error_feasible_comparator
#print axioms actual_solver_mathematical_guarantee
end
end Reference.LexOrderedTensorSolver