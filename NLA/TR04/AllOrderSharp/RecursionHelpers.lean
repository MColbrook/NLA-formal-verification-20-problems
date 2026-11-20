module

public import NLA.TR04.AllOrderSharp.Merge
public import NLA.TR04.LexicographicTensorCompletion.ProcessCorrectness

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp
open Reference.LexTensorCompletion

@[simp] theorem mul_prefixInclusion {m n : ℕ}
    (V : Matrix (Fin m) (Fin (n+1)) ℝ) (i : Fin m) (b : Fin n) :
    (V * prefixInclusion n) i b = V i b.castSucc := by
  simp [Matrix.mul_apply, prefixInclusion]

theorem tag_mul_diagonal {m n N : ℕ} (hN : n ≤ N)
    (W : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    tag hN (W * Matrix.diagonal c) = tag hN W * Matrix.diagonal c := by
  ext p b
  simp only [tag, Matrix.mul_diagonal]
  split_ifs <;> simp

theorem family_compress {N q m k : ℕ} (hN : q+2 ≤ N)
    (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin m) (Fin (q+2)) ℝ) :
    U.transpose * family hN V = family hN (U.transpose * V) := by
  unfold family
  exact (Matrix.mul_assoc _ _ _).symm

theorem merge_compressed_weighted_family {N q m k : ℕ} (hN : q+3 ≤ N)
    (U : Matrix (Fin m) (Fin k) ℝ) (V : Matrix (Fin m) (Fin (q+3)) ℝ)
    (c : Fin (q+3) → ℝ)
    (hlast : ∀ i, (U.transpose * V) i (Fin.last (q+2)) = 0) :
    merge (U.transpose * family hN (V * Matrix.diagonal c)) =
      family (show q+2 ≤ N by omega)
        (tag (show q+2 ≤ N by omega) (U.transpose * (V * prefixInclusion (q+2))) *
          Matrix.diagonal (fun b => c b.castSucc)) := by
  rw [family_compress, ← Matrix.mul_assoc]
  rw [merge_family_last_zero hN _ (fun i => by simp [Matrix.mul_diagonal, hlast i])]
  congr 1
  rw [← tag_mul_diagonal]
  congr 1
  ext i b
  simp only [Matrix.mul_diagonal, ← Matrix.mul_assoc, mul_prefixInclusion]

theorem keep_mask_zero_weight {n : ℕ} (i₀ : Fin n) (c : Fin n → ℝ) (hc : c i₀ = 0) :
    Matrix.diagonal (keepMask i₀) * Matrix.diagonal c = Matrix.diagonal c := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i = i₀
  · subst i; simp [keepMask, hc]
  · simp [keepMask, hi]

theorem projected_zero_weight_family {N q m k : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (U : Matrix (Fin m) (Fin k) ℝ)
    (i₀ : Fin (q+2))
    (hp : U * U.transpose * V = V * Matrix.diagonal (keepMask i₀))
    (c : Fin (q+2) → ℝ) (hc : c i₀ = 0) :
    U * U.transpose * family hN (V * Matrix.diagonal c) =
      family hN (V * Matrix.diagonal c) := by
  unfold family
  calc
    _ = (U * U.transpose * V) * Matrix.diagonal c * selector hN := by
      simp only [Matrix.mul_assoc]
    _ = (V * Matrix.diagonal (keepMask i₀)) * Matrix.diagonal c * selector hN := by rw [hp]
    _ = (V * Matrix.diagonal c) * selector hN := by
      rw [Matrix.mul_assoc V _ _, keep_mask_zero_weight i₀ c hc]

def originWeight (a : ℝ) {n : ℕ} (b : Fin (n+1)) : ℝ :=
  if b.val = 0 then a else 0

def remainingRanks : ℕ → List ℕ
  | 0 => []
  | q+1 => ranks q

theorem ranks_cons (q : ℕ) : ranks q = (q+1) :: remainingRanks q := by
  cases q <;> rfl

theorem ordinary_as_completion {N q m : ℕ} (hN : q+2 ≤ N)
    (A : Tensor m (List.replicate (q+1) N)) :
    ttSVD m (List.replicate (q+1) N) A (ranks q) =
      completeFrame A (svdFrame A (q+1)) (remainingRanks q) := by
  rw [ranks_cons]
  simp only [List.replicate_succ, ttSVD, completeFrame]

theorem optimal_first_frame_error {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (hV : V.transpose * V = 1)
    (c : Fin (q+2) → ℝ) :
    let A := family hN (V * Matrix.diagonal c)
    Reference.TensorGrouping.entryFrobeniusSq
      (A - svdFrame A (q+1) * (svdFrame A (q+1)).transpose * A) ≤ c (Fin.last (q+1)) ^ 2 := by
  let A := family hN (V * Matrix.diagonal c)
  let Y := family hN
    (V * Matrix.diagonal (fun i => if i = Fin.last (q+1) then 0 else c i))
  have hY : Y.rank ≤ q+1 := by
    apply family_rank_column_zero hN _ (Fin.last (q+1))
    intro i
    simp [Matrix.mul_diagonal]
  have hb := (svdFrame_correct A (q+1)).2 Y hY
  have he : tensorFrobeniusSq (A-Y) = c (Fin.last (q+1)) ^ 2 :=
    family_single_row_error hN V hV c (Fin.last (q+1))
  rw [he] at hb
  exact hb

#print axioms optimal_first_frame_error

end NLA.TR04.AllOrderSharp
