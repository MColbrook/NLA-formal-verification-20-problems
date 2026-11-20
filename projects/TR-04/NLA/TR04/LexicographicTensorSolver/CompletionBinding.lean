module

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Cyclic spectral candidates fed to the exact named actual TT-SVD completion. -/
public import NLA.TR04.LexicographicTensorSolver.CompletionDefinitions
public import NLA.TR04.LexicographicTensorSolver.CyclicOptimality
public import NLA.TR04.LexicographicTensorCompletion.ProcessCorrectness

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexTensorCompletion Reference.TensorGrouping
open scoped Matrix BigOperators

theorem denseTensor_frobenius {m : ℕ} {ns : List ℕ} (A : Tensor m ns) :
    frobeniusSq (denseTensor A)=tensorFrobeniusSq A := by
  change entryFrobeniusSq (A.submatrix id (concreteLayout ns).symm)=entryFrobeniusSq A
  exact entryFrobeniusSq_reindex_columns (concreteLayout ns) A

theorem denseTensor_mul {m k : ℕ} {ns : List ℕ} (V : Rect k m) (A : Tensor m ns) :
    denseTensor (V*A)=V*denseTensor A := rfl

theorem denseTensor_sub {m : ℕ} {ns : List ℕ} (A B : Tensor m ns) :
    denseTensor (A-B)=denseTensor A-denseTensor B := rfl

theorem actual_tied_cyclic_completion_bound {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length)
    (hr : 0<r) (hrank : r<(denseTensor A).rank) (hY : feasible m (n::ns) Y (r::rs))
    (hequal : tensorFrobeniusSq (A-Y)=singularTailSq (denseTensor A) r) :
    ∃ j : Fin (tensorBoundaryCount A r),
      feasible m (n::ns) (cyclicCompletion A r rs j) (r::rs) ∧
      tensorFrobeniusSq (A-cyclicCompletion A r rs j) ≤ singularTailSq (denseTensor A) r+
        (ns.length : ℝ)*(tensorRetainedBoundary A r : ℝ)/(tensorBoundaryCount A r : ℝ)*tensorFrobeniusSq (A-Y) := by
  classical
  let A0 := denseTensor A
  let Y0 := denseTensor Y
  let tau := singularValue A0 (r-1)
  let s := r-hCount A0 tau
  have hFirst : Y.rank ≤ r := by simp only [feasible] at hY;exact hY.1
  have hY0 : Y0.rank ≤ r := (Matrix.rank_submatrix_le Y id (concreteLayout (n::ns)).symm).trans hFirst
  have hErr : frobeniusSq (A0-Y0)=tensorFrobeniusSq (A-Y) := by
    rw [← denseTensor_sub]
    exact denseTensor_frobenius (A-Y)
  have hbest : ∀ C : Rect m (Fintype.card (ModeIndex (n::ns))), C.rank ≤ r →
      frobeniusSq (A0-Y0) ≤ frobeniusSq (A0-C) := by
    intro C hC
    rw [hErr,hequal]
    exact singularTail_le_lowRankError A0 C r hC
  obtain ⟨j,havg⟩ := actual_best_rank_cyclic_candidate_residual_bound A0 Y0 r hr hrank hY0 hbest
  let U := candidateFrame A0 tau s j
  let k := Fintype.card {i : Fin m // selected A0 tau s j i}
  have hFacts := actual_cyclic_frame_dimension_and_optimality A0 r hr hrank j
  have hU : U.transpose*U=1 := hFacts.2.1
  have hk : k ≤ r := hFacts.1.le
  have hP : U*U.transpose=candidateProjector A0 tau s j := (actual_candidate_frame A0 tau s j).2
  have hInitial : tensorFrobeniusSq (A-U*U.transpose*A)=singularTailSq A0 r := by
    calc
      _ = frobeniusSq (denseTensor (A-U*U.transpose*A)) := (denseTensor_frobenius _).symm
      _ = frobeniusSq (A0-candidateProjector A0 tau s j*A0) := by
        rw [denseTensor_sub,denseTensor_mul,hP]
      _ = _ := hFacts.2.2.1
  have hProjected : tensorFrobeniusSq (U*U.transpose*(A-Y)) ≤
      (s : ℝ)/(eCount A0 tau : ℝ)*tensorFrobeniusSq (A-Y) := by
    calc
      _ = frobeniusSq (denseTensor (U*U.transpose*(A-Y))) := (denseTensor_frobenius _).symm
      _ = frobeniusSq (candidateProjector A0 tau s j*(A0-Y0)) := by
        rw [denseTensor_mul,hP,denseTensor_sub]
      _ ≤ (s : ℝ)/(eCount A0 tau : ℝ)*frobeniusSq (A0-Y0) := havg
      _ = _ := by rw [hErr]
  have hComplete := completeFrame_correct A U hU r rs hlen hk
  have hb := (hComplete.2 Y hY).2
  have hw := mul_le_mul_of_nonneg_left hProjected (show (0 : ℝ) ≤ (ns.length : ℝ) by exact Nat.cast_nonneg _)
  refine ⟨j,hComplete.1,?_⟩
  calc
    _ ≤ tensorFrobeniusSq (A-U*U.transpose*A)+(ns.length : ℝ)*tensorFrobeniusSq (U*U.transpose*(A-Y)) := hb
    _ ≤ singularTailSq A0 r+(ns.length : ℝ)*((s : ℝ)/(eCount A0 tau : ℝ)*tensorFrobeniusSq (A-Y)) := by
      rw [hInitial]
      exact add_le_add le_rfl hw
    _ = _ := by dsimp [tensorRetainedBoundary,tensorBoundaryCount,tensorBoundary,s,tau,A0];ring

theorem actual_partial_tie_strict_completion {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length)
    (hr : 0<r) (hrank : r<(denseTensor A).rank) (hY : feasible m (n::ns) Y (r::rs))
    (hequal : tensorFrobeniusSq (A-Y)=singularTailSq (denseTensor A) r)
    (hpositive : 0<tensorFrobeniusSq (A-Y)) (hns : 0<ns.length)
    (hpartial : tensorRetainedBoundary A r<tensorBoundaryCount A r) :
    ∃ j : Fin (tensorBoundaryCount A r), feasible m (n::ns) (cyclicCompletion A r rs j) (r::rs) ∧
      tensorFrobeniusSq (A-cyclicCompletion A r rs j)<((ns.length : ℝ)+1)*tensorFrobeniusSq (A-Y) := by
  obtain ⟨j,hj,hb⟩ := actual_tied_cyclic_completion_bound A Y r rs hlen hr hrank hY hequal
  have ht : (0 : ℝ)<(tensorBoundaryCount A r : ℝ) := by exact_mod_cast (Nat.zero_le _).trans_lt hpartial
  have hc : (tensorRetainedBoundary A r : ℝ)/(tensorBoundaryCount A r : ℝ)<1 := by
    rw [div_lt_one ht]
    exact_mod_cast hpartial
  have hn : (0 : ℝ)<(ns.length : ℝ) := by exact_mod_cast hns
  have hm := mul_lt_mul_of_pos_left hc (mul_pos hn hpositive)
  refine ⟨j,hj,?_⟩
  rw [← hequal] at hb
  have he : (ns.length : ℝ)*(tensorRetainedBoundary A r : ℝ)/(tensorBoundaryCount A r : ℝ)*tensorFrobeniusSq (A-Y)=
      ((ns.length : ℝ)*tensorFrobeniusSq (A-Y))*((tensorRetainedBoundary A r : ℝ)/(tensorBoundaryCount A r : ℝ)) := by ring
  rw [he] at hb
  nlinarith

#print axioms actual_tied_cyclic_completion_bound
#print axioms actual_partial_tie_strict_completion
end
end Reference.LexOrderedCyclicBoundary