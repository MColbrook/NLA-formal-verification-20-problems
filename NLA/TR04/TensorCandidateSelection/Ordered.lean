module

/- Earliest minimum behavior and exact branch-specific candidate lists. -/
public import NLA.TR04.TensorCandidateSelection.Strict

@[expose] public section

set_option autoImplicit false
namespace Reference.TensorCandidateSelection
noncomputable section
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion Reference.CyclicBoundary

theorem firstMinimum_earliest_position {m : ℕ} {ns : List ℕ}
    (A acc x : Tensor m ns) (pre post : List (Tensor m ns))
    (hacc : error A x<error A acc) (hpre : ∀ y ∈ pre, error A x<error A y)
    (hpost : ∀ y ∈ post, error A x ≤ error A y) :
    firstMinimum A acc (pre++x::post)=x := by
  classical
  induction pre generalizing acc with
  | nil =>
    simp only [List.nil_append,firstMinimum,if_pos hacc]
    exact firstMinimum_first_tie A x post hpost
  | cons y ys ih =>
    simp only [List.cons_append,firstMinimum]
    split_ifs
    · exact ih y (hpre y (by simp)) (fun z hz => hpre z (List.mem_cons_of_mem y hz))
    · exact ih acc hacc (fun z hz => hpre z (List.mem_cons_of_mem y hz))

theorem rank_le_candidate_list {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : (denseTensor A).rank ≤ r) :
    candidates A r rs=[columnSpaceCompletion A rs] := by
  classical
  simp only [candidates,if_pos hRank]

theorem full_tie_candidate_list {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : r<(denseTensor A).rank)
    (ht : 0<tensorBoundaryCount A r) (hfull : tensorRetainedBoundary A r=tensorBoundaryCount A r) :
    candidates A r rs=[cyclicCompletion A r rs ⟨0,ht⟩] := by
  classical
  simp only [candidates,if_neg (not_le_of_gt hRank),dif_pos ht,if_pos hfull]

theorem partial_tie_candidate_list {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : r<(denseTensor A).rank)
    (ht : 0<tensorBoundaryCount A r) (hpartial : tensorRetainedBoundary A r<tensorBoundaryCount A r) :
    candidates A r rs=List.ofFn (cyclicCompletion A r rs) := by
  classical
  simp only [candidates,if_neg (not_le_of_gt hRank),dif_pos ht,if_neg (ne_of_lt hpartial)]

#print axioms firstMinimum_earliest_position
#print axioms rank_le_candidate_list
#print axioms full_tie_candidate_list
#print axioms partial_tie_candidate_list
end
end Reference.TensorCandidateSelection