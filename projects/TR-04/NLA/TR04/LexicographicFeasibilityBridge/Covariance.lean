module

/- Covariance of the actual frozen recursive feasible set under finite row permutations. -/
public import NLA.TR04.LexicographicFeasibilityBridge.Definitions
public import NLA.TR04.RecursiveTensorCompletion.Regrouping

@[expose] public section

set_option autoImplicit false
namespace Reference.LexicographicFeasibilityBridge
noncomputable section
open Reference.RecursiveTensorCompletion

theorem rank_rowPermutation {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (e : Fin m ≃ Fin m) : (A.submatrix e id).rank = A.rank := by
  exact Matrix.rank_submatrix A e (Equiv.refl (ModeIndex ns))

theorem merge_rowPermutation {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (e : Fin m ≃ Fin m) :
    merge (A.submatrix e id) = (merge A).submatrix (inducedRowPermutation n e) id := by
  ext i j
  simp [merge, inducedRowPermutation, Matrix.submatrix]
  rfl

theorem feasible_rowPermutation {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (e : Fin m ≃ Fin m) (rs : List ℕ) :
    feasible m ns (A.submatrix e id) rs ↔ feasible m ns A rs := by
  induction ns generalizing m rs with
  | nil => simp only [feasible]
  | cons n ns ih =>
    cases rs with
    | nil => simp only [feasible]
    | cons r rs =>
      simp only [feasible]
      rw [rank_rowPermutation, merge_rowPermutation]
      exact and_congr Iff.rfl (ih (merge A) (inducedRowPermutation n e) rs)

#print axioms rank_rowPermutation
#print axioms merge_rowPermutation
#print axioms feasible_rowPermutation
end
end Reference.LexicographicFeasibilityBridge
