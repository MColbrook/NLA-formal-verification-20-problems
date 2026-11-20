module

public import NLA.RA02.PaperDiagonalUpdate
public import NLA.RA02.PaperHeadBounds

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem diagonalPivotUpdate_diag {n : ℕ} (a : Fin n → ℝ) (v : Fin n → ℂ) (d : ℝ) (i : Fin n) :
    (diagonalPivotUpdate a v d i i).re = a i - a i ^ 2 * Complex.normSq (v i) / d := by
  have he : diagonalPivotUpdate a v d i i =
      ((a i - a i ^ 2 * Complex.normSq (v i) / d : ℝ) : ℂ) := by
    simp only [diagonalPivotUpdate, Matrix.sub_apply, Matrix.diagonal_apply_eq,
      Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Pi.star_apply,
      star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_sub,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    ring
  rw [he, Complex.ofReal_re]

theorem diagonalPivotUpdate_diag_le {n : ℕ} (a : Fin n → ℝ) (v : Fin n → ℂ)
    (d : ℝ) (hd : 0 ≤ d) (i : Fin n) : (diagonalPivotUpdate a v d i i).re ≤ a i := by
  rw [diagonalPivotUpdate_diag]
  exact sub_le_self _ (div_nonneg (mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)) hd)

theorem diagonalPivotUpdate_exists_probe {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (v : Fin n → ℂ) (b c : ℝ)
    (hb : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i*Complex.normSq (v i) = b)
    (hc : 0 ≤ c) (hd : 0 < b+c) :
    ∃ g : Fin n → ℂ, (∀ i, k ≤ i.val → g i = 0) ∧ (∑ i, Complex.normSq (g i) = 1) ∧
      (b+c) * (star g ⬝ᵥ (diagonalPivotUpdate a v (b+c) *ᵥ g)).re ≤ (∑ i, a i)*c := by
  by_cases hh : 0 < headEnergy k v
  · refine ⟨headProbe k v, headProbe_supported k v, headProbe_norm k v hh, ?_⟩
    rw [diagonalPivotUpdate_head_quadratic k a v b c hh (ne_of_gt hd) hb, Complex.ofReal_re]
    have hbnd := weighted_head_le_total k a v ha
    rw [hb] at hbnd
    have he : (b+c)*(b*c/(headEnergy k v*(b+c))) = b*c/headEnergy k v := by
      field_simp
    rw [he]
    apply (div_le_iff₀ hh).mpr
    nlinarith [mul_le_mul_of_nonneg_right hbnd hc]
  · have hh0 : headEnergy k v = 0 := le_antisymm (le_of_not_gt hh) (headEnergy_nonneg k v)
    have hb0 : b = 0 := by rw [← hb]; exact weighted_head_eq_zero k a v ha hh0
    let i0 : Fin n := ⟨0, by omega⟩
    let g : Fin n → ℂ := Pi.single i0 1
    refine ⟨g, ?_, ?_, ?_⟩
    · intro i hi
      have hne : i ≠ i0 := by intro he; subst i; simp only [i0] at hi; omega
      simp [g, Pi.single_apply, hne, Ne.symm hne]
    · simp [g, Pi.single_apply]
    · have he : star g ⬝ᵥ (diagonalPivotUpdate a v (b+c) *ᵥ g) =
          diagonalPivotUpdate a v (b+c) i0 i0 := by
        simp [g, dotProduct, Matrix.mulVec, Pi.single_apply, Pi.star_apply]
      rw [he]
      have hbnd := (diagonalPivotUpdate_diag_le a v (b+c) hd.le i0).trans (eigenvalue_le_total a ha i0)
      simpa [hb0, mul_comm] using mul_le_mul_of_nonneg_left hbnd hd.le

#print axioms diagonalPivotUpdate_exists_probe
end NLA.RA02.Paper
