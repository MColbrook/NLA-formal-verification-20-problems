module

public import NLA.MF05.PaperRealNorm
public import NLA.MF07.TriangularDamping

@[expose] public section

set_option autoImplicit false
open NLA.MF07
noncomputable section
namespace NLA.MF05.Paper

lemma complexify_diagonal {d : ℕ} (h : Fin d → ℝ) :
    complexify (Matrix.diagonal h) = diagonalWeights h := by
  ext i j
  by_cases hij : i = j <;> simp [complexify, diagonalWeights, Matrix.diagonal_apply, hij]

theorem real_triangular_damping {d : ℕ} (h : Fin d → ℝ) (hh : Antitone h)
    (hpos : ∀ i, 0 < h i) (X : RealSquare d)
    (hX : ∀ i j, h j < h i → X i j = 0) :
    realSpectralNorm (Matrix.diagonal h * X * Matrix.diagonal (fun i => (h i)⁻¹)) ≤
      realSpectralNorm X := by
  have hx : LowerForWeights h (complexify X) := by
    intro i j hij
    simp [complexify, hX i j hij]
  have hc := triangular_damping h hh hpos (complexify X) hx
  have he : complexify (Matrix.diagonal h * X * Matrix.diagonal (fun i => (h i)⁻¹)) =
      diagonalDamping h (complexify X) := by
    rw [map_mul, map_mul, complexify_diagonal, complexify_diagonal]
    simp only [diagonalDamping, diagonalWeights, inverseDiagonalWeights, Complex.ofReal_inv]
  rw [← he, complexify_spectralNorm, complexify_spectralNorm] at hc
  exact hc

theorem complex_block_damping {d b : ℕ} (block : Fin d → Fin b) (hblock : Monotone block)
    (h : Fin b → ℝ) (hh : Antitone h) (hpos : ∀ i, 0 < h i)
    (X : Square d) (hX : ∀ i j, block i < block j → X i j = 0) :
    spectralNorm (diagonalWeights (h ∘ block) * X * (diagonalWeights (h ∘ block))⁻¹) ≤
      spectralNorm X := by
  have hx : LowerForWeights (h ∘ block) X := by
    intro i j hij
    apply hX i j
    by_contra hn
    have hc := hh (le_of_not_gt hn)
    exact (not_lt_of_ge hc) hij
  rw [Matrix.inv_eq_left_inv (diagonal_inverse (h ∘ block) (fun i => (hpos (block i)).ne')).2]
  exact
    triangular_damping (h ∘ block) (hh.comp_monotone hblock) (fun i => hpos (block i)) X hx

theorem real_block_damping {d b : ℕ} (block : Fin d → Fin b) (hblock : Monotone block)
    (h : Fin b → ℝ) (hh : Antitone h) (hpos : ∀ i, 0 < h i)
    (X : RealSquare d) (hX : ∀ i j, block i < block j → X i j = 0) :
    realSpectralNorm (Matrix.diagonal (h ∘ block) * X *
      (Matrix.diagonal (h ∘ block))⁻¹) ≤ realSpectralNorm X := by
  have hinv : Matrix.diagonal (fun i => (h (block i))⁻¹) * Matrix.diagonal (h ∘ block) = 1 := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij, (hpos _).ne']
  rw [Matrix.inv_eq_left_inv hinv]
  apply real_triangular_damping (h ∘ block) (hh.comp_monotone hblock)
    (fun i => hpos (block i)) X
  intro i j hij
  apply hX i j
  by_contra hn
  have hc := hh (le_of_not_gt hn)
  exact (not_lt_of_ge hc) hij

#print axioms complex_block_damping
#print axioms real_block_damping
end NLA.MF05.Paper
