module

/- Changing actual product equivalences at every recursive merge preserves feasibility. -/
public import NLA.TR04.LexicographicFeasibilityBridge.Covariance

@[expose] public section

set_option autoImplicit false
namespace Reference.LexicographicFeasibilityBridge
noncomputable section
open Reference.RecursiveTensorCompletion

theorem mergeWith_eq_submatrix (layout : RowLayout) {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) :
    mergeWith layout A = (merge A).submatrix (layoutPermutation layout m n) id := by
  ext i j
  simp [mergeWith, merge, layoutPermutation, Matrix.submatrix]

theorem feasibleWith_iff_feasible (layout : RowLayout) {m : ℕ} {ns : List ℕ}
    (A : Tensor m ns) (rs : List ℕ) :
    feasibleWith layout m ns A rs ↔ feasible m ns A rs := by
  induction ns generalizing m rs with
  | nil => simp only [feasibleWith, feasible]
  | cons n ns ih =>
    cases rs with
    | nil => simp only [feasibleWith, feasible]
    | cons r rs =>
      simp only [feasibleWith, feasible]
      refine and_congr Iff.rfl ?_
      rw [ih, mergeWith_eq_submatrix]
      exact feasible_rowPermutation (merge A) (layoutPermutation layout m n) rs

theorem mergeLex_eq_submatrix {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) :
    mergeLex A = (merge A).submatrix (layoutPermutation rowEquivLex m n) id :=
  mergeWith_eq_submatrix rowEquivLex A

theorem feasibleLex_iff_feasible {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (rs : List ℕ) : feasibleLex m ns A rs ↔ feasible m ns A rs := by
  induction ns generalizing m rs with
  | nil => simp only [feasibleLex, feasible]
  | cons n ns ih =>
    cases rs with
    | nil => simp only [feasibleLex, feasible]
    | cons r rs =>
      simp only [feasibleLex, feasible]
      refine and_congr Iff.rfl ?_
      rw [ih, mergeLex_eq_submatrix]
      exact feasible_rowPermutation (merge A) (layoutPermutation rowEquivLex m n) rs

theorem feasibleLex_rowPermutation {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (e : Fin m ≃ Fin m) (rs : List ℕ) :
    feasibleLex m ns (A.submatrix e id) rs ↔ feasibleLex m ns A rs := by
  rw [feasibleLex_iff_feasible, feasibleLex_iff_feasible]
  exact feasible_rowPermutation A e rs

theorem feasibleWith_iff_layout (layout₁ layout₂ : RowLayout) {m : ℕ} {ns : List ℕ}
    (A : Tensor m ns) (rs : List ℕ) :
    feasibleWith layout₁ m ns A rs ↔ feasibleWith layout₂ m ns A rs := by
  rw [feasibleWith_iff_feasible, feasibleWith_iff_feasible]

#print axioms mergeWith_eq_submatrix
#print axioms feasibleWith_iff_feasible
#print axioms mergeLex_eq_submatrix
#print axioms feasibleLex_iff_feasible
#print axioms feasibleLex_rowPermutation
#print axioms feasibleWith_iff_layout
end
end Reference.LexicographicFeasibilityBridge
