module

public import NLA.RA02.ComplexHistoryPaths

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper.ComplexHistory

def completedHistoryEquiv {k : ℕ} (rows : Fin k ↪ Fin (k+1))
    (p : Fin (k+1)) (hp : p ∉ Set.range rows) : Fin (k+1) ≃ Fin (k+1) :=
  Equiv.ofBijective (appendEmbedding rows p hp)
    ⟨(appendEmbedding rows p hp).injective,
      Finite.surjective_of_injective (appendEmbedding rows p hp).injective⟩

theorem mem_history_or_last {k : ℕ} (rows : Fin k ↪ Fin (k+1))
    (p : Fin (k+1)) (hp : p ∉ Set.range rows) (i : Fin (k+1)) :
    i ∈ Set.range rows ∨ i = p := by
  obtain ⟨j,hj⟩ := (completedHistoryEquiv rows p hp).surjective i
  induction j using Fin.lastCases with
  | last =>
    right
    simpa [completedHistoryEquiv, appendEmbedding] using hj.symm
  | cast j =>
    left
    exact ⟨j, by simpa [completedHistoryEquiv, appendEmbedding] using hj⟩

theorem terminal_residual_support {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℂ)
    (rows cols : Fin k ↪ Fin (k+1)) (p q : Fin (k+1))
    (hp : p ∉ Set.range rows) (hq : q ∉ Set.range cols)
    (hu : IsUnit (A.submatrix rows cols)) (i j : Fin (k+1)) :
    interpolatoryResidual A rows cols i j =
      if i = p ∧ j = q then interpolatoryResidual A rows cols p q else 0 := by
  by_cases hip : i = p
  · subst i
    by_cases hjq : j = q
    · subst j; simp
    · obtain ⟨l,hl⟩ := (mem_history_or_last cols q hq j).resolve_right hjq
      rw [if_neg (by tauto), ← hl]
      exact residual_selected_column A rows cols hu p l
  · obtain ⟨l,hl⟩ := (mem_history_or_last rows p hp i).resolve_right hip
    rw [if_neg (by tauto), ← hl]
    exact residual_selected_row A rows cols hu l j

theorem terminal_trace_entry {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℂ)
    (rows : Fin k ↪ Fin (k+1)) (p : Fin (k+1)) (hp : p ∉ Set.range rows)
    (hu : IsUnit (A.submatrix rows rows)) :
    (interpolatoryResidual A rows rows).trace = interpolatoryResidual A rows rows p p := by
  simp only [Matrix.trace, Matrix.diag]
  calc
    _ = ∑ i, if i = p then interpolatoryResidual A rows rows p p else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [and_self] using terminal_residual_support A rows rows p p hp hp hu i i
    _ = _ := by simp

theorem terminal_trace_det {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℂ)
    (rows : Fin k ↪ Fin (k+1)) (p : Fin (k+1)) (hp : p ∉ Set.range rows)
    (hu : IsUnit (A.submatrix rows rows)) :
    (A.submatrix rows rows).det * (interpolatoryResidual A rows rows).trace = A.det := by
  rw [terminal_trace_entry A rows p hp hu, ← residual_bordered_determinant A rows rows p p hp hp hu]
  exact Matrix.det_submatrix_equiv_self (completedHistoryEquiv rows p hp) A

theorem normSq_det_submatrix_equiv (n : ℕ) (e₁ e₂ : Fin n ≃ Fin n) (A : NLA.RA02.Square n) :
    Complex.normSq (A.submatrix e₁ e₂).det = Complex.normSq A.det := by
  have hee : e₂ = e₁.trans (e₁.symm.trans e₂) := by ext; simp
  rw [hee]
  change Complex.normSq ((A.submatrix id (e₁.symm.trans e₂)).submatrix e₁ e₁).det = _
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_permute', map_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e₁.symm.trans e₂)) with h | h <;> simp [h]

theorem terminal_frobenius_entry {k : ℕ} (A : NLA.RA02.Square (k+1))
    (rows cols : Fin k ↪ Fin (k+1)) (p q : Fin (k+1))
    (hp : p ∉ Set.range rows) (hq : q ∉ Set.range cols)
    (hu : IsUnit (A.submatrix rows cols)) :
    NLA.RA03.frobeniusSq (interpolatoryResidual A rows cols) =
      Complex.normSq (interpolatoryResidual A rows cols p q) := by
  unfold NLA.RA03.frobeniusSq
  calc
    _ = ∑ i, ∑ j, Complex.normSq (if i = p ∧ j = q then interpolatoryResidual A rows cols p q else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [terminal_residual_support A rows cols p q hp hq hu i j]
    _ = _ := by simp [ite_and, apply_ite]

theorem terminal_frobenius_det {k : ℕ} (A : NLA.RA02.Square (k+1))
    (rows cols : Fin k ↪ Fin (k+1)) (p q : Fin (k+1))
    (hp : p ∉ Set.range rows) (hq : q ∉ Set.range cols)
    (hu : IsUnit (A.submatrix rows cols)) :
    Complex.normSq (A.submatrix rows cols).det *
      NLA.RA03.frobeniusSq (interpolatoryResidual A rows cols) = Complex.normSq A.det := by
  rw [terminal_frobenius_entry A rows cols p q hp hq hu, ← map_mul,
    ← residual_bordered_determinant A rows cols p q hp hq hu]
  exact normSq_det_submatrix_equiv (k+1) (completedHistoryEquiv rows p hp) (completedHistoryEquiv cols q hq) A

end NLA.RA02.Paper.ComplexHistory
