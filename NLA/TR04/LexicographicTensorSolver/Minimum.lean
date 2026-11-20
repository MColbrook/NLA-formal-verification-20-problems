module

/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Correctness and tie behavior of literal ordered first-minimum scan. -/
public import NLA.TR04.LexicographicTensorSolver.SolverDefinitions
public import NLA.TR04.LexicographicTensorSolver.FullCompletion

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedTensorSolver
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary

theorem firstMinimum_mem {m : ℕ} {ns : List ℕ} (A x : Tensor m ns)
    (xs : List (Tensor m ns)) : firstMinimum A x xs ∈ x::xs := by
  classical
  induction xs generalizing x with
  | nil => simp [firstMinimum]
  | cons y ys ih =>
    simp only [firstMinimum]
    split_ifs with h
    · exact List.mem_cons_of_mem x (ih y)
    · rcases List.mem_cons.mp (ih x) with hh|hh
      · exact List.mem_cons.mpr (Or.inl hh)
      · exact List.mem_cons.mpr (Or.inr (List.mem_cons_of_mem y hh))

theorem firstMinimum_le {m : ℕ} {ns : List ℕ} (A x : Tensor m ns)
    (xs : List (Tensor m ns)) : ∀ y ∈ x::xs, error A (firstMinimum A x xs) ≤ error A y := by
  classical
  induction xs generalizing x with
  | nil =>
    intro y hy
    simp only [List.mem_singleton] at hy
    subst y
    exact le_rfl
  | cons y ys ih =>
    intro z hz
    simp only [firstMinimum]
    split_ifs with h
    · rcases List.mem_cons.mp hz with hz|hz
      · subst z
        exact (ih y y (by simp)).trans h.le
      · exact ih y z hz
    · rcases List.mem_cons.mp hz with hz|hz
      · subst z;exact ih x x (by simp)
      · rcases List.mem_cons.mp hz with hz|hz
        · subst z
          exact (ih x x (by simp)).trans (le_of_not_gt h)
        · exact ih x z (List.mem_cons_of_mem x hz)

theorem firstMinimum_first_tie {m : ℕ} {ns : List ℕ} (A x : Tensor m ns)
    (xs : List (Tensor m ns)) (hx : ∀ y ∈ xs, error A x ≤ error A y) :
    firstMinimum A x xs=x := by
  classical
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    rw [firstMinimum,if_neg (not_lt_of_ge (hx y (by simp)))]
    exact ih (fun z hz => hx z (List.mem_cons_of_mem y hz))

theorem candidates_nonempty {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (r : ℕ) (rs : List ℕ) : candidates A r rs ≠ [] := by
  classical
  unfold candidates
  split_ifs with h ht hf
  · simp
  · simp
  · intro he
    have hl := congrArg List.length he
    simp only [List.length_ofFn,List.length_nil] at hl
    omega
  · simp

theorem solver_mem {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :
    solver A r rs ∈ candidates A r rs := by
  have hn := candidates_nonempty A r rs
  unfold solver
  generalize he : candidates A r rs=xs at hn ⊢
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons x xs => exact firstMinimum_mem A x xs

theorem solver_dominates {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :
    ∀ X ∈ candidates A r rs, error A (solver A r rs) ≤ error A X := by
  have hn := candidates_nonempty A r rs
  unfold solver
  generalize he : candidates A r rs=xs at hn ⊢
  cases xs with
  | nil => exact False.elim (hn rfl)
  | cons x xs => exact firstMinimum_le A x xs

theorem actual_completion_count_le_first_mode {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 0<m) :
    (candidates A r rs).length ≤ m := by
  classical
  unfold candidates
  split_ifs
  · simpa using (Nat.succ_le_of_lt hm)
  · simpa using (Nat.succ_le_of_lt hm)
  · simp only [List.length_ofFn]
    exact actual_boundary_candidate_count_le (denseTensor A) (tensorBoundary A r)
  · simpa using (Nat.succ_le_of_lt hm)

#print axioms firstMinimum_mem
#print axioms firstMinimum_le
#print axioms firstMinimum_first_tie
#print axioms solver_mem
#print axioms solver_dominates
#print axioms actual_completion_count_le_first_mode
end
end Reference.LexOrderedTensorSolver