module

public import NLA.TR04.AllOrderSharp.Merge

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp
open Reference.LexTensorCompletion

def eraseColumn {m n : ℕ} (V : Matrix (Fin m) (Fin n) ℝ) (i0 : Fin n) :
    Matrix (Fin m) (Fin n) ℝ := fun i b => if b = i0 then 0 else V i b

theorem family_sub {N q m : ℕ} (hN : q+2 ≤ N)
    (V W : Matrix (Fin m) (Fin (q+2)) ℝ) :
    family hN (V-W) = family hN V - family hN W := by
  exact Matrix.sub_mul V W (selector hN)

theorem eraseColumn_error {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (i0 : Fin (q+2)) :
    tensorFrobeniusSq (family hN V - family hN (eraseColumn V i0)) = ∑ i, V i i0 ^ 2 := by
  rw [← family_sub, family_norm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i0]
  · simp [eraseColumn]
  · intro b _ hb
    simp [eraseColumn, hb]
  · simp

theorem erase_nuisance_feasible {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) :
    feasible m (List.replicate (q+1) N)
      (family hN (eraseColumn V ⟨1, by omega⟩)) (ranks q) := by
  apply family_nuisance_zero_feasible
  intro i
  simp [eraseColumn]

theorem weighted_nuisance_energy {q m : ℕ}
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (hV : V.transpose * V = 1)
    (c : Fin (q+2) → ℝ) :
    (∑ i, (V * Matrix.diagonal c) i ⟨1, by omega⟩ ^ 2) = c ⟨1, by omega⟩ ^ 2 := by
  have hh := congrArg (fun M => M (⟨1, by omega⟩ : Fin (q+2)) ⟨1, by omega⟩) hV
  have hnorm : (∑ i, V i ⟨1, by omega⟩ ^ 2) = 1 := by
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, if_pos rfl, if_true,
      ← pow_two] using hh
  simp only [Matrix.mul_diagonal, mul_pow]
  rw [← Finset.sum_mul, hnorm, one_mul]

theorem weighted_optimal_candidate {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ) (hV : V.transpose * V = 1)
    (c : Fin (q+2) → ℝ) :
    ∃ Y : Tensor m (List.replicate (q+1) N),
      feasible m (List.replicate (q+1) N) Y (ranks q) ∧
      tensorFrobeniusSq (family hN (V * Matrix.diagonal c) - Y) = c ⟨1, by omega⟩ ^ 2 := by
  refine ⟨family hN (eraseColumn (V * Matrix.diagonal c) ⟨1, by omega⟩),
    erase_nuisance_feasible hN _, ?_⟩
  rw [eraseColumn_error]
  exact weighted_nuisance_energy V hV c

end NLA.TR04.AllOrderSharp
