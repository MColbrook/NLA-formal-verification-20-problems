module

public import NLA.RA02.PaperHeadProbe

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

def diagonalPivotUpdate {n : ℕ} (a : Fin n → ℝ) (v : Fin n → ℂ) (d : ℝ) :
    NLA.RA02.Square n :=
  Matrix.diagonal (fun i => (a i : ℂ)) -
    (d : ℂ)⁻¹ • Matrix.vecMulVec (fun i => (a i : ℂ)*v i) (star (fun i => (a i : ℂ)*v i))

theorem diagonalPivotUpdate_quadratic {n : ℕ} (a : Fin n → ℝ) (v g : Fin n → ℂ) (d : ℝ) :
    star g ⬝ᵥ (diagonalPivotUpdate a v d *ᵥ g) =
      (∑ i, (a i : ℂ)*star (g i)*g i) -
        (∑ i, star (g i)*((a i : ℂ)*v i)) *
          star (∑ i, star (g i)*((a i : ℂ)*v i)) / (d : ℂ) := by
  have hs : (∑ i, star ((a i : ℂ)*v i)*g i) =
      star (∑ i, star (g i)*((a i : ℂ)*v i)) := by
    simp only [star_sum, star_mul, star_star, mul_assoc]
  simp only [diagonalPivotUpdate, Matrix.sub_mulVec, dotProduct_sub,
    Matrix.smul_mulVec, dotProduct_smul, Matrix.vecMulVec_mulVec, Matrix.mulVec_diagonal]
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, op_smul_eq_mul, Matrix.mulVec_diagonal]
  rw [Finset.sum_mul, hs]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    ring
  · simp only [Finset.sum_mul, mul_assoc]
    ring

theorem diagonalPivotUpdate_head_quadratic {n : ℕ} (k : ℕ) (a : Fin n → ℝ)
    (v : Fin n → ℂ) (b c : ℝ) (hh : 0 < headEnergy k v) (hd : b+c ≠ 0)
    (hb : ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i*Complex.normSq (v i) = b) :
    star (headProbe k v) ⬝ᵥ (diagonalPivotUpdate a v (b+c) *ᵥ headProbe k v) =
      ((b*c/(headEnergy k v*(b+c)) : ℝ) : ℂ) := by
  rw [diagonalPivotUpdate_quadratic, headProbe_weighted_inner, headProbe_weighted_norm k a v hh, hb]
  have hs : (Real.sqrt (headEnergy k v) : ℂ)^2 = (headEnergy k v : ℂ) := by
    exact_mod_cast Real.sq_sqrt hh.le
  have hs0 : (Real.sqrt (headEnergy k v) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hh)
  have hh0 : (headEnergy k v : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hh
  have hd0 : ((b+c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  simp only [map_div₀, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_div, Complex.ofReal_mul]
  rw [← hs]
  field_simp
  <;> simp only [Complex.ofReal_add]
  <;> ring

#print axioms diagonalPivotUpdate_head_quadratic
end NLA.RA02.Paper
