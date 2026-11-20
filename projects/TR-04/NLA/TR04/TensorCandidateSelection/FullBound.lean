module

/- Cyclic spectral candidates fed to the exact named actual TT-SVD completion. -/
public import NLA.TR04.TensorCandidateSelection.Candidates

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.TensorCandidateSelection
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.CyclicBoundary Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RecursiveTensorCompletion Reference.TensorGrouping
open scoped Matrix BigOperators

theorem every_full_tie_completion_bound {m n : ℕ} {ns : List ℕ}
    (A Y : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length)
    (hr : 0<r) (hrank : r<(denseTensor A).rank) (hY : feasible m (n::ns) Y (r::rs))
    (hequal : tensorFrobeniusSq (A-Y)=singularTailSq (denseTensor A) r)
    (hfull : tensorRetainedBoundary A r=tensorBoundaryCount A r)
    (j : Fin (tensorBoundaryCount A r)) :
      feasible m (n::ns) (cyclicCompletion A r rs j) (r::rs) ∧
      tensorFrobeniusSq (A-cyclicCompletion A r rs j) ≤ tensorFrobeniusSq (A-Y) := by
  classical
  let A0 := denseTensor A
  let Y0 := denseTensor Y
  let tau := singularValue A0 (r-1)
  let s := r-hCount A0 tau
  have hFirst : Y.rank ≤ r := by simp only [feasible] at hY;exact hY.1
  have hY0 : Y0.rank ≤ r := (Matrix.rank_submatrix_le Y id (Fintype.equivFin (ModeIndex (n::ns))).symm).trans hFirst
  have hErr : frobeniusSq (A0-Y0)=tensorFrobeniusSq (A-Y) := by
    rw [← denseTensor_sub]
    exact denseTensor_frobenius (A-Y)
  have hbest : ∀ C : Rect m (Fintype.card (ModeIndex (n::ns))), C.rank ≤ r →
      frobeniusSq (A0-Y0) ≤ frobeniusSq (A0-C) := by
    intro C hC
    rw [hErr,hequal]
    exact singularTail_le_lowRankError A0 C r hC
  have hAnn := actual_full_tie_candidate_annihilates A0 Y0 r hr hrank hY0 hbest hfull j
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
  have hProjected : tensorFrobeniusSq (U*U.transpose*(A-Y))=0 := by
    calc
      _ = frobeniusSq (denseTensor (U*U.transpose*(A-Y))) := (denseTensor_frobenius _).symm
      _ = frobeniusSq (candidateProjector A0 tau s j*(A0-Y0)) := by
        rw [denseTensor_mul,hP,denseTensor_sub]
      _ = 0 := by rw [hAnn];simp [frobeniusSq]
  have hComplete := completeFrame_correct A U hU r rs hlen hk
  have hb := (hComplete.2 Y hY).2
  refine ⟨hComplete.1,?_⟩
  rw [hProjected,hInitial] at hb
  simp only [mul_zero,add_zero] at hb
  rw [← hequal] at hb
  exact hb

#print axioms every_full_tie_completion_bound
end
end Reference.TensorCandidateSelection
