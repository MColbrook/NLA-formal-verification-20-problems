module

public import NLA.TR04.AllOrderSharp.RecursionHelpers
public import NLA.TR04.AllOrderSharp.Coefficients

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp
open Reference.LexTensorCompletion

/-- Every optimal first-frame completion of this family returns its root
branch. The induction uses the actual recursively defined TT-SVD, and permits
every orthonormal basis of each selected singular subspace. -/
theorem every_completion_exact (q : ℕ) :
    ∀ {N m k : ℕ} (hN : q+2 ≤ N)
      (V : Matrix (Fin m) (Fin (q+2)) ℝ) (hV : V.transpose * V = 1)
      (c : ℕ → ℝ) (hpos : ∀ i, 0 < c i) (hanti : StrictAnti (fun i => c i ^ 2))
      (U : Matrix (Fin m) (Fin k) ℝ) (hU : U.transpose * U = 1) (hk : k ≤ q+1)
      (he : Reference.TensorGrouping.entryFrobeniusSq
        (family hN (V * Matrix.diagonal (fun b => c b.val)) -
          U * U.transpose * family hN (V * Matrix.diagonal (fun b => c b.val))) ≤
            c (q+1) ^ 2),
      completeFrame (family hN (V * Matrix.diagonal (fun b => c b.val))) U
        (remainingRanks q) = family hN (V * Matrix.diagonal (originWeight (c 0))) := by
  induction q with
  | zero =>
      intro N m k hN V hV c hpos hanti U hU hk he
      have hp := weighted_family_projection hN V hV (fun b => c b.val)
        (fun b => hpos b.val) (fun _ _ hij => hanti hij) U (by omega) he
      have hd : Matrix.diagonal (keepMask (Fin.last 1)) *
          Matrix.diagonal (fun b : Fin 2 => c b.val) =
            Matrix.diagonal (originWeight (c 0)) := by
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext b
        fin_cases b <;> simp [keepMask, originWeight, Fin.ext_iff]
      simp only [remainingRanks, completeFrame, List.replicate_succ,
        List.replicate_zero, ttSVD, unmerge_merge]
      calc
        _ = (U * U.transpose * V) * Matrix.diagonal (fun b => c b.val) * selector hN := by
          simp only [family, Matrix.mul_assoc]
        _ = (V * Matrix.diagonal (keepMask (Fin.last 1))) *
            Matrix.diagonal (fun b => c b.val) * selector hN := by rw [hp]
        _ = family hN (V * Matrix.diagonal (originWeight (c 0))) := by
          rw [Matrix.mul_assoc V _ _, hd]
          rfl
  | succ q ih =>
      intro N m k hN V hV c hpos hanti U hU hk he
      have hN' : q+2 ≤ N := by omega
      have hp := weighted_family_projection hN V hV (fun b => c b.val)
        (fun b => hpos b.val) (fun _ _ hij => hanti hij) U (by omega) he
      have hz := compressed_last_zero V U hU hp
      let W := U.transpose * (V * prefixInclusion (q+2))
      have hW : W.transpose * W = 1 := retained_frame_orthonormal V hV U hp
      let T := tag hN' W
      have hT : T.transpose * T = 1 := tag_orthonormal hN' W hW
      let C := family hN' (T * Matrix.diagonal (fun b => c b.val))
      have hmerge : merge (U.transpose * family hN
          (V * Matrix.diagonal (fun b => c b.val))) = C :=
        merge_compressed_weighted_family hN U V (fun b => c b.val) hz
      let U' := svdFrame C (q+1)
      have hU' : U'.transpose * U' = 1 := (svdFrame_correct C (q+1)).1
      have he' : Reference.TensorGrouping.entryFrobeniusSq
          (C - U' * U'.transpose * C) ≤ c (q+1) ^ 2 :=
        optimal_first_frame_error hN' T hT (fun b => c b.val)
      have hrec := ih hN' T hT c hpos hanti U' hU' (Nat.min_le_left _ _) he'
      have hord : ttSVD (rowCount k N) (List.replicate (q+1) N) C (ranks q) =
          family hN' (T * Matrix.diagonal (originWeight (c 0))) := by
        rw [ordinary_as_completion hN' C]
        exact hrec
      have hmerge0 : merge (U.transpose * family hN
          (V * Matrix.diagonal (originWeight (c 0)))) =
            family hN' (T * Matrix.diagonal (originWeight (c 0))) :=
        merge_compressed_weighted_family hN U V (originWeight (c 0)) hz
      simp only [remainingRanks, completeFrame]
      rw [hmerge, hord, ← hmerge0, unmerge_merge]
      have hfix := projected_zero_weight_family hN V U (Fin.last (q+2)) hp
        (originWeight (c 0)) (by simp [originWeight])
      simpa only [Matrix.mul_assoc] using hfix

/-- Exact output of the literal ordinary recursive TT-SVD for every order. -/
theorem ordinary_exact {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (hV : V.transpose * V = 1)
    (c : ℕ → ℝ) (hpos : ∀ i, 0 < c i) (hanti : StrictAnti (fun i => c i ^ 2)) :
    ttSVD m (List.replicate (q+1) N)
      (family hN (V * Matrix.diagonal (fun b => c b.val))) (ranks q) =
        family hN (V * Matrix.diagonal (originWeight (c 0))) := by
  let A := family hN (V * Matrix.diagonal (fun b => c b.val))
  rw [ordinary_as_completion hN]
  apply every_completion_exact q hN V hV c hpos hanti (svdFrame A (q+1))
    (svdFrame_correct A (q+1)).1 (Nat.min_le_left _ _)
  exact optimal_first_frame_error hN V hV (fun b => c b.val)

#print axioms every_completion_exact
#print axioms ordinary_exact

end NLA.TR04.AllOrderSharp
