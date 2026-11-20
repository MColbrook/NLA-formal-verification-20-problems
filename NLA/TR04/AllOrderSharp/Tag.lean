module

public import NLA.TR04.AllOrderSharp.RetainedFrame

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp
open Reference.LexTensorCompletion

/-- Attach a distinct next-mode coordinate to each retained branch. -/
def tag {m n N : ℕ} (_hN : n ≤ N) (W : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (rowCount m N)) (Fin n) ℝ :=
  fun p b => if ((rowEquiv m N).symm p).2.val = b.val then
    W ((rowEquiv m N).symm p).1 b else 0

theorem tag_gram {m n N : ℕ} (hN : n ≤ N) (W : Matrix (Fin m) (Fin n) ℝ) :
    (tag hN W).transpose * tag hN W =
      Matrix.diagonal (fun b => ∑ i, W i b ^ 2) := by
  classical
  let w : Fin m → Fin n → ℝ := fun i j => W i j
  ext a b
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  change (∑ p, (if ((rowEquiv m N).symm p).2.val = a.val then
      w ((rowEquiv m N).symm p).1 a else 0) *
    (if ((rowEquiv m N).symm p).2.val = b.val then
      w ((rowEquiv m N).symm p).1 b else 0)) = if a = b then ∑ i, w i a ^ 2 else 0
  rw [(rowEquiv m N).symm.sum_comp (fun p : Fin m × Fin N =>
    (if p.2.val = a.val then w p.1 a else 0) *
      (if p.2.val = b.val then w p.1 b else 0))]
  rw [Fintype.sum_prod_type]
  by_cases hab : a = b
  · subst b
    simp only [ite_true]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (⟨a.val, a.isLt.trans_le hN⟩ : Fin N)]
    · simp [pow_two]
    · intro j _ hj
      have hval : j.val ≠ a.val := by
        intro heq
        apply hj
        exact Fin.ext heq
      simp [hval]
    · simp
  · have hval : a.val ≠ b.val := fun hh => hab (Fin.ext hh)
    simp only [if_neg hab]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    by_cases hja : j.val = a.val
    · simp [hja, hval]
    · simp [hja]

theorem tag_orthonormal {m n N : ℕ} (hN : n ≤ N)
    (W : Matrix (Fin m) (Fin n) ℝ) (hW : W.transpose * W = 1) :
    (tag hN W).transpose * tag hN W = 1 := by
  rw [tag_gram]
  have hnorm : ∀ b, (∑ i, W i b ^ 2) = 1 := by
    intro b
    have hh := congrArg (fun A => A b b) hW
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hh
  ext a b
  simp [Matrix.diagonal_apply, Matrix.one_apply, hnorm]

#print axioms tag_orthonormal

end NLA.TR04.AllOrderSharp
