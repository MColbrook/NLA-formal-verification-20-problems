module

/- Genuine mathematical bounds for every actual completion candidate. -/
public import NLA.TR04.TensorCandidateSelection.Minimum

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.TensorCandidateSelection
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealColumnCompression Reference.RealOptimalityEquality Reference.RecursiveTensorCompletion Reference.CyclicBoundary
open scoped Matrix

theorem denseTensor_rank {m : ℕ} {ns : List ℕ} (A : Tensor m ns) :
    (denseTensor A).rank=A.rank := by
  exact Matrix.rank_submatrix A (Equiv.refl (Fin m)) (Fintype.equivFin (ModeIndex ns)).symm

theorem tensorFrobeniusSq_nonneg {m : ℕ} {ns : List ℕ} (A : Tensor m ns) :
    0 ≤ tensorFrobeniusSq A := by
  rw [← denseTensor_frobenius]
  exact frobeniusSq_nonneg _

theorem leadingFrame_projection_error {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) :
    tensorFrobeniusSq (A-svdFrame A r*(svdFrame A r).transpose*A)=singularTailSq (denseTensor A) r := by
  let A0 := denseTensor A
  let V := leftVectorMatrix A0
  have hU : svdFrame A r=firstColumns V r := rfl
  have hP : svdFrame A r*(svdFrame A r).transpose=leftLeadingProjector A0 r := by
    rw [hU,firstColumns_projection]
    rfl
  calc
    _ = frobeniusSq (denseTensor (A-svdFrame A r*(svdFrame A r).transpose*A)) := (denseTensor_frobenius _).symm
    _ = frobeniusSq (A0-leftLeadingProjector A0 r*A0) := by rw [denseTensor_sub,denseTensor_mul,hP]
    _ = _ := actual_leading_projection_error A0 r

theorem leadingCompletion_feasible_and_bound {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) :
    feasible m (n::ns) (leadingCompletion A r rs) (r::rs) ∧
      ∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) →
      error A (leadingCompletion A r rs) ≤ singularTailSq (denseTensor A) r+
        (ns.length : ℝ)*error A Y := by
  have hU := (svdFrame_correct A r).1
  have hC := completeFrame_correct A (svdFrame A r) hU r rs hlen (Nat.min_le_left r m)
  refine ⟨hC.1,?_⟩
  intro Y hY
  have hb := (hC.2 Y hY).1
  rw [leadingFrame_projection_error] at hb
  exact hb.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (tensor_compression_frobenius_le _ hU (A-Y)) (Nat.cast_nonneg _)))

theorem columnSpaceCompletion_feasible_and_bound {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length)
    (hRank : (denseTensor A).rank ≤ r) :
    feasible m (n::ns) (columnSpaceCompletion A rs) (r::rs) ∧
      ∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) →
      error A (columnSpaceCompletion A rs) ≤ singularTailSq (denseTensor A) r+
        (ns.length : ℝ)*error A Y := by
  let q := (denseTensor A).rank
  let U := svdFrame A q
  have hU := (svdFrame_correct A q).1
  have hProj := (svdFrame_correct A q).2 A (by rw [← denseTensor_rank])
  have hz : tensorFrobeniusSq (A-U*U.transpose*A)=0 := by
    apply le_antisymm
    · simpa [tensorFrobeniusSq] using hProj
    · exact tensorFrobeniusSq_nonneg _
  have ht : 0 ≤ singularTailSq (denseTensor A) r := by
    rw [← leadingFrame_projection_error]
    exact tensorFrobeniusSq_nonneg _
  have hk : min q m ≤ r := (Nat.min_le_left q m).trans hRank
  have hC := completeFrame_correct A U hU r rs hlen hk
  refine ⟨hC.1,?_⟩
  intro Y hY
  have hb := (hC.2 Y hY).1
  rw [hz,zero_add] at hb
  calc
    _ ≤ (ns.length : ℝ)*error A Y := hb.trans
      (mul_le_mul_of_nonneg_left (tensor_compression_frobenius_le U hU (A-Y)) (Nat.cast_nonneg _))
    _ ≤ _ := le_add_of_nonneg_left ht

theorem cyclicCompletion_feasible_and_bound {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length)
    (hr : 0<r) (hrank : r<(denseTensor A).rank) (j : Fin (tensorBoundaryCount A r)) :
    feasible m (n::ns) (cyclicCompletion A r rs j) (r::rs) ∧
      ∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) →
      error A (cyclicCompletion A r rs j) ≤ singularTailSq (denseTensor A) r+
        (ns.length : ℝ)*error A Y := by
  let A0 := denseTensor A
  let tau := tensorBoundary A r
  let s := tensorRetainedBoundary A r
  let U := tensorCandidateFrame A r j
  have hF := actual_cyclic_frame_dimension_and_optimality A0 r hr hrank j
  have hU : U.transpose*U=1 := hF.2.1
  have hk := hF.1.le
  have hP : U*U.transpose=candidateProjector A0 tau s j := (actual_candidate_frame A0 tau s j).2
  have hi : tensorFrobeniusSq (A-U*U.transpose*A)=singularTailSq A0 r := by
    calc
      _ = frobeniusSq (denseTensor (A-U*U.transpose*A)) := (denseTensor_frobenius _).symm
      _ = frobeniusSq (A0-candidateProjector A0 tau s j*A0) := by rw [denseTensor_sub,denseTensor_mul,hP]
      _ = _ := hF.2.2.1
  have hC := completeFrame_correct A U hU r rs hlen hk
  refine ⟨hC.1,?_⟩
  intro Y hY
  have hb := (hC.2 Y hY).1
  rw [hi] at hb
  exact hb.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (tensor_compression_frobenius_le _ hU (A-Y)) (Nat.cast_nonneg _)))

theorem candidate_feasible_and_bound {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (X : Tensor m (n::ns)) (hX : X ∈ candidates A r rs) :
    feasible m (n::ns) X (r::rs) ∧
      ∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) →
      error A X ≤ singularTailSq (denseTensor A) r+(ns.length : ℝ)*error A Y := by
  classical
  unfold candidates at hX
  split_ifs at hX with hRank ht hf
  · simp only [List.mem_singleton] at hX
    subst X
    exact columnSpaceCompletion_feasible_and_bound A r rs hlen hRank
  · simp only [List.mem_singleton] at hX
    subst X
    exact cyclicCompletion_feasible_and_bound A r rs hlen hr (lt_of_not_ge hRank) _
  · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hX
    exact cyclicCompletion_feasible_and_bound A r rs hlen hr (lt_of_not_ge hRank) j
  · simp only [List.mem_singleton] at hX
    subst X
    exact leadingCompletion_feasible_and_bound A r rs hlen

theorem solver_feasible_and_bound {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r) :
    feasible m (n::ns) (solver A r rs) (r::rs) ∧
      ∀ Y : Tensor m (n::ns), feasible m (n::ns) Y (r::rs) →
      error A (solver A r rs) ≤ singularTailSq (denseTensor A) r+(ns.length : ℝ)*error A Y :=
  candidate_feasible_and_bound A r rs hlen hr _ (solver_mem A r rs)

theorem solver_exact_for_feasible_input {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hA : feasible m (n::ns) A (r::rs)) : solver A r rs=A := by
  have hFirst : A.rank ≤ r := by simp only [feasible] at hA;exact hA.1
  have hProj := (svdFrame_correct A r).2 A hFirst
  have hz : tensorFrobeniusSq (A-svdFrame A r*(svdFrame A r).transpose*A)=0 := by
    have hn := tensorFrobeniusSq_nonneg (A-svdFrame A r*(svdFrame A r).transpose*A)
    have hh : tensorFrobeniusSq (A-A)=0 := by simp [tensorFrobeniusSq]
    rw [hh] at hProj
    exact le_antisymm hProj hn
  have ht := leadingFrame_projection_error A r
  have hb := (solver_feasible_and_bound A r rs hlen hr).2 A hA
  rw [← ht,hz] at hb
  have hsame : error A (solver A r rs)=0 := by
    apply le_antisymm
    · simpa [error,tensorFrobeniusSq] using hb
    · exact tensorFrobeniusSq_nonneg _
  have hzero : denseTensor (A-solver A r rs)=0 := (frobeniusSq_eq_zero_iff _).mp
    (by rw [denseTensor_frobenius];exact hsame)
  have h := congrArg (fun M => M.submatrix id (Fintype.equivFin (ModeIndex (n::ns)))) hzero
  have hs : A-solver A r rs=0 := by simpa [denseTensor,Matrix.submatrix_submatrix] using h
  exact (sub_eq_zero.mp hs).symm

#print axioms columnSpaceCompletion_feasible_and_bound
#print axioms leadingCompletion_feasible_and_bound
#print axioms cyclicCompletion_feasible_and_bound
#print axioms solver_feasible_and_bound
#print axioms solver_exact_for_feasible_input
end
end Reference.TensorCandidateSelection