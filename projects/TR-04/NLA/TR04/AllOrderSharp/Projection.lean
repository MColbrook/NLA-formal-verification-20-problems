module

public import NLA.TR04.AllOrderSharp.EmbeddedRows

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp
open Reference.TensorGrouping

variable {m n k : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

def keepMask (i₀ : Fin n) (i : Fin n) : ℝ := if i = i₀ then 0 else 1

theorem drop_row_eq_diagonal (D : Matrix (Fin n) κ ℝ) (i₀ : Fin n) :
    (fun i j => if i = i₀ then 0 else D i j) = Matrix.diagonal (keepMask i₀) * D := by
  ext i j
  by_cases hi : i = i₀ <;> simp [Matrix.diagonal_mul, keepMask, hi]

/-- The row-orthogonality identity gives a genuine right inverse whenever every
row has positive energy. -/
theorem orthogonal_rows_right_inverse (D : Matrix (Fin n) κ ℝ) (w : Fin n → ℝ)
    (hgram : ∀ i j, (∑ b, D i b * D j b) = if i = j then w i else 0)
    (hpos : ∀ i, 0 < w i) :
    D * (D.transpose * Matrix.diagonal (fun i => (w i)⁻¹)) = 1 := by
  have hg : D * D.transpose = Matrix.diagonal w := by
    ext i j
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
      using hgram i j
  rw [← Matrix.mul_assoc, hg, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j; simp [ne_of_gt (hpos i)]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem embedded_full_rank (V : Matrix (Fin m) (Fin n) ℝ)
    (hV : V.transpose * V = 1) (D : Matrix (Fin n) κ ℝ)
    (w : Fin n → ℝ)
    (hgram : ∀ i j, (∑ b, D i b * D j b) = if i = j then w i else 0)
    (hpos : ∀ i, 0 < w i) : (V * D).rank = n := by
  let R := D.transpose * Matrix.diagonal (fun i => (w i)⁻¹)
  have hright : D * R = 1 := orthogonal_rows_right_inverse D w hgram hpos
  have hinv : V.transpose * (V * D) * R = 1 := by
    rw [← Matrix.mul_assoc V.transpose V D, hV, Matrix.one_mul, hright]
  apply le_antisymm
  · exact (Matrix.rank_mul_le_left V D).trans (Matrix.rank_le_width V)
  · calc
      n = (1 : Matrix (Fin n) (Fin n) ℝ).rank := by simp
      _ = (V.transpose * (V * D) * R).rank := by rw [hinv]
      _ ≤ (V.transpose * (V * D)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (V * D).rank := Matrix.rank_mul_le_right _ _

/-- The actual optimal projector fixes every retained row direction and kills
the strictly smallest direction. Its choice of orthonormal basis is irrelevant.
-/
theorem actual_projection_on_embedding (V : Matrix (Fin m) (Fin n) ℝ)
    (hV : V.transpose * V = 1) (D : Matrix (Fin n) κ ℝ)
    (w : Fin n → ℝ)
    (hgram : ∀ i j, (∑ b, D i b * D j b) = if i = j then w i else 0)
    (hpos : ∀ i, 0 < w i) (i₀ : Fin n)
    (hsmall : ∀ i, i ≠ i₀ → w i₀ < w i)
    (U : Matrix (Fin m) (Fin k) ℝ) (hk : k < n)
    (herror : entryFrobeniusSq (V * D - U * U.transpose * (V * D)) ≤ w i₀) :
    U * U.transpose * V = V * Matrix.diagonal (keepMask i₀) := by
  have hrank : (U * U.transpose * (V * D)).rank < n :=
    (Matrix.rank_mul_le_left _ _).trans_lt
      ((Matrix.rank_mul_le_left _ _).trans_lt
        ((Matrix.rank_le_width U).trans_lt hk))
  have hp := embedded_smallest_row_unique V hV D w hgram i₀ hsmall
    (U * U.transpose * (V * D)) hrank herror
  rw [drop_row_eq_diagonal] at hp
  change U * U.transpose * (V * D) = V * (Matrix.diagonal (keepMask i₀) * D) at hp
  let R := D.transpose * Matrix.diagonal (fun i => (w i)⁻¹)
  have hright : D * R = 1 := orthogonal_rows_right_inverse D w hgram hpos
  have hm := congrArg (fun A : Matrix (Fin m) κ ℝ => A * R) hp
  simpa only [Matrix.mul_assoc, hright, Matrix.mul_one] using hm

/-- Retained directions remain orthonormal after compression by the actual
frame, including all possible signs and rotations of that frame. -/
theorem retained_compression_orthonormal (V : Matrix (Fin m) (Fin n) ℝ)
    (hV : V.transpose * V = 1) (U : Matrix (Fin m) (Fin k) ℝ)
    {r : ℕ} (J : Matrix (Fin n) (Fin r) ℝ) (hJ : J.transpose * J = 1)
    (hfix : U * U.transpose * (V * J) = V * J) :
    (U.transpose * (V * J)).transpose * (U.transpose * (V * J)) = 1 := by
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = (V * J).transpose * (U * U.transpose * (V * J)) := by
      simp only [Matrix.mul_assoc]
    _ = (V * J).transpose * (V * J) := by rw [hfix]
    _ = J.transpose * (V.transpose * V) * J := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hV, Matrix.mul_one, hJ]

#print axioms actual_projection_on_embedding
#print axioms retained_compression_orthonormal

end NLA.TR04.AllOrderSharp
