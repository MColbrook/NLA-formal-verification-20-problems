module

public import NLA.TR04.AllOrderSharp.RecursionHelpers
public import NLA.TR04.AllOrderSharp.OptimalCandidate
public import NLA.TR04.AllOrderSharp.Coefficients
public import NLA.TR04.LexicographicTensorSolver.Strict

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp
open Reference.LexTensorCompletion Reference.LexOrderedTensorSolver

theorem family_diagonal_norm {N q : ℕ} (hN : q+2 ≤ N) (c : Fin (q+2) → ℝ) :
    tensorFrobeniusSq (family hN (Matrix.diagonal c)) = ∑ b, c b ^ 2 := by
  rw [family_norm]
  simp [Matrix.diagonal_apply]

theorem root_branch_error {N q : ℕ} (hN : q+2 ≤ N) (c : ℕ → ℝ) :
    tensorFrobeniusSq (family hN (Matrix.diagonal (fun b => c b.val)) -
      family hN (Matrix.diagonal (originWeight (c 0)))) =
        ∑ b : Fin (q+1), c (b.val+1) ^ 2 := by
  have hd : Matrix.diagonal (fun b : Fin (q+2) => c b.val) -
      Matrix.diagonal (originWeight (c 0)) =
        Matrix.diagonal (fun b => if b.val = 0 then 0 else c b.val) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal_apply, originWeight]
      split_ifs <;> simp_all
    · simp [Matrix.diagonal_apply, hij]
  rw [← family_sub, hd, family_diagonal_norm, Fin.sum_univ_succ]
  simp

theorem ranks_length (q : ℕ) : (ranks q).length = q+1 := by
  induction q with
  | zero => rfl
  | succ q ih => simp [ranks, ih]

theorem remainingRanks_length (q : ℕ) : (remainingRanks q).length = q := by
  cases q with
  | zero => rfl
  | succ q => exact ranks_length q

theorem fixed_order_strict (q : ℕ) (hq : 0 < q)
    (A Y : Tensor (q+2) (List.replicate (q+1) (q+2)))
    (hY : feasible (q+2) (List.replicate (q+1) (q+2)) Y (ranks q))
    (hpositive : 0 < tensorFrobeniusSq (A-Y)) :
    tensorFrobeniusSq (Sub.sub A (solver A (q+1) (remainingRanks q))) <
      ((q+1 : ℕ) : ℝ) * tensorFrobeniusSq (A-Y) := by
  have hy' : feasible (q+2) (List.replicate (q+1) (q+2)) Y
      ((q+1) :: remainingRanks q) := by
    simpa only [ranks_cons] using hY
  have hs := solver_strict_against_every_positive_feasible_comparator A Y
    (q+1) (remainingRanks q)
    (by simp [remainingRanks_length]) (by omega)
    (by simpa using hq) hy' hpositive
  simp only [error, List.length_replicate, Nat.cast_add, Nat.cast_one] at hs
  convert hs using 1
  all_goals first | rfl | simp only [Nat.cast_add, Nat.cast_one]

#print axioms fixed_order_strict

#print axioms root_branch_error

end NLA.TR04.AllOrderSharp
