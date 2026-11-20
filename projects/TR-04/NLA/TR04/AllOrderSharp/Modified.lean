module

public import NLA.TR04.AllOrderSharp.Algorithm
public import NLA.TR04.LexicographicTensorSolver.Strict

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp
open Reference.LexTensorCompletion Reference.LexOrderedTensorSolver
open Reference.LexOrderedCyclicBoundary Reference.RealSVDPackage

theorem weighted_family_full_rank {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (hV : V.transpose * V = 1)
    (c : ℕ → ℝ) (hpos : ∀ i, 0 < c i) :
    (family hN (V * Matrix.diagonal (fun b => c b.val))).rank = q+2 := by
  rw [family_weighted_embedding]
  exact embedded_full_rank V hV (family hN (Matrix.diagonal (fun b => c b.val)))
    (fun b => c b.val ^ 2) (weighted_selector_row_gram hN _)
    (fun b => sq_pos_of_pos (hpos b.val))

/-- The literal modified solver has the same root-branch output at every order.
The proof covers every candidate in its actual finite candidate list. -/
theorem modified_exact {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (hV : V.transpose * V = 1)
    (c : ℕ → ℝ) (hpos : ∀ i, 0 < c i) (hanti : StrictAnti (fun i => c i ^ 2)) :
    solver (m := m) (n := N) (ns := List.replicate q N)
      (family hN (V * Matrix.diagonal (fun b => c b.val))) (q+1)
      (remainingRanks q) = family hN (V * Matrix.diagonal (originWeight (c 0))) := by
  let A : Tensor m (N :: List.replicate q N) :=
    family hN (V * Matrix.diagonal (fun b => c b.val))
  have hrank : q+1 < (denseTensor A).rank := by
    rw [denseTensor_rank, weighted_family_full_rank hN V hV c hpos]
    omega
  have hcyclic : ∀ j : Fin (tensorBoundaryCount A (q+1)),
      cyclicCompletion (m := m) (n := N) (ns := List.replicate q N)
        A (q+1) (remainingRanks q) j =
          family hN (V * Matrix.diagonal (originWeight (c 0))) := by
    intro j
    let A0 := denseTensor A
    let tau := tensorBoundary A (q+1)
    let s := tensorRetainedBoundary A (q+1)
    let U := tensorCandidateFrame A (q+1) j
    have hF := actual_cyclic_frame_dimension_and_optimality A0 (q+1) (by omega) hrank j
    have hU : U.transpose * U = 1 := hF.2.1
    have hP : U * U.transpose = candidateProjector A0 tau s j :=
      (actual_candidate_frame A0 tau s j).2
    have hdense : denseTensor (A - U * U.transpose * A) =
        A0 - candidateProjector A0 tau s j * A0 := by
      calc
        _ = denseTensor A - denseTensor (U * U.transpose * A) :=
          denseTensor_sub A (U * U.transpose * A)
        _ = A0 - (U * U.transpose) * A0 :=
          congrArg (fun M : Rect m (Fintype.card (ModeIndex (N :: List.replicate q N))) =>
            A0-M) (denseTensor_mul (U * U.transpose) A)
        _ = _ := congrArg (fun P : Square m => A0-P*A0) hP
    have he : Reference.TensorGrouping.entryFrobeniusSq (A - U * U.transpose * A) ≤
        c (q+1) ^ 2 := by
      calc
        _ = frobeniusSq (denseTensor (A - U * U.transpose * A)) :=
          (denseTensor_frobenius _).symm
        _ = frobeniusSq (A0 - candidateProjector A0 tau s j * A0) :=
          congrArg frobeniusSq hdense
        _ = singularTailSq A0 (q+1) := hF.2.2.1
        _ = tensorFrobeniusSq
            (A - svdFrame A (q+1) * (svdFrame A (q+1)).transpose * A) :=
          (leadingFrame_projection_error A (q+1)).symm
        _ ≤ c (q+1) ^ 2 := optimal_first_frame_error hN V hV (fun b => c b.val)
    exact every_completion_exact q hN V hV c hpos hanti U hU hF.1.le he
  have hall : ∀ X ∈ candidates A (q+1) (remainingRanks q),
      X = family hN (V * Matrix.diagonal (originWeight (c 0))) := by
    intro X hx
    unfold candidates at hx
    rw [if_neg (not_le_of_gt hrank)] at hx
    split_ifs at hx with ht hf
    · simp only [List.mem_singleton] at hx
      rw [hx]
      exact hcyclic _
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hcyclic j
    · simp only [List.mem_singleton] at hx
      rw [hx]
      simpa only [leadingCompletion, ordinary_as_completion hN] using
        ordinary_exact hN V hV c hpos hanti
  exact hall _ (solver_mem A (q+1) (remainingRanks q))

#print axioms modified_exact

end NLA.TR04.AllOrderSharp
