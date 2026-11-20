module

public import NLA.RA08.LiteralJoins.NormLaws
public import NLA.RA08.LiteralContour.NuclearBlock
public import NLA.RA08.LiteralContour.NuclearDistance

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper.LiteralJoins

theorem actual_nuclear_off_diagonal_norm (m : ℕ) (hm : 1 ≤ m) :
    nuclearNorm (LiteralContour.nuclearOffDiagonal m)=nuclearNorm (nuclearKernel m)/m := by
  change nuclearNorm ((1/(2*m) : ℝ) • symmetricDilation (nuclearKernel m))=_
  rw [nuclearNorm_smul,symmetricDilation_nuclearNorm,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/(2*m))]
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  field_simp

theorem actual_nuclear_derivative_kernel_bound (m : ℕ) (hm : 1 ≤ m) :
    nuclearNorm (nuclearKernel m)/m ≤ nuclearNorm (nuclearDerivative m) := by
  rw [← actual_nuclear_off_diagonal_norm m hm]
  exact LiteralContour.actual_nuclear_block_pinching m

theorem nuclear_error_bound {m : ℕ} (E : RealMatrix m)
    (hE : frobeniusSquared E ≤ 2*m/15) :
    nuclearNorm E ≤ m*Real.sqrt (2/15) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hq : (Real.sqrt m*frobeniusNorm E)^2 ≤ ((m : ℝ)*Real.sqrt (2/15))^2 := by
    rw [mul_pow,Real.sq_sqrt hm,← frobeniusSquared_norm,
      mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2/15)]
    nlinarith [mul_le_mul_of_nonneg_left hE hm]
  have hb := (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (frobeniusNorm_nonneg E))
    (by positivity : 0 ≤ (m : ℝ)*Real.sqrt (2/15))).mp hq
  exact (nuclearNorm_frobenius_bound E).trans hb

theorem actual_nuclear_kernel_triangular_lower (m : ℕ) :
    nuclearNorm (nuclearTriangular m)-(m : ℝ)/2-m*Real.sqrt (2/15) ≤
      nuclearNorm (nuclearKernel m) := by
  let E := nuclearKernel m-(nuclearTriangular m-(1/2 : ℝ) • (1 : RealMatrix m))
  have he : nuclearNorm E ≤ m*Real.sqrt (2/15) :=
    nuclear_error_bound E (nuclearTriangular_error_frobenius_squared m)
  have hi : nuclearNorm ((1/2 : ℝ) • (1 : RealMatrix m))=(m : ℝ)/2 := by
    rw [nuclearNorm_smul,nuclearNorm_one]
    norm_num
    ring
  have h : nuclearNorm (nuclearTriangular m) ≤
      nuclearNorm (nuclearKernel m)+nuclearNorm E+(m : ℝ)/2 := by
    calc
      _ = nuclearNorm (nuclearKernel m-E+(1/2 : ℝ) • (1 : RealMatrix m)) := by
        congr 1
        dsimp only [E]
        abel
      _ ≤ nuclearNorm (nuclearKernel m-E)+nuclearNorm ((1/2 : ℝ) • (1 : RealMatrix m)) :=
        nuclearNorm_triangle _ _
      _ ≤ nuclearNorm (nuclearKernel m)+nuclearNorm E+(m : ℝ)/2 := by
        rw [hi]
        linarith [nuclearNorm_sub (nuclearKernel m) E]
  linarith

theorem actual_nuclear_kernel_triangular_ratio (m : ℕ) (hm : 1 ≤ m) :
    nuclearNorm (nuclearTriangular m)/m-1/2-
      Real.sqrt (2*(1/4 : ℝ)^2/(1-(1/4 : ℝ)^2)) ≤ nuclearNorm (nuclearKernel m)/m := by
  have hp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have h := (div_le_div_iff_of_pos_right hp).mpr (actual_nuclear_kernel_triangular_lower m)
  have hn := ne_of_gt hp
  have hc : 2*(1/4 : ℝ)^2/(1-(1/4 : ℝ)^2)=2/15 := by norm_num
  rw [hc]
  have he : nuclearNorm (nuclearTriangular m)/m-1/2-Real.sqrt (2/15) =
      (nuclearNorm (nuclearTriangular m)-(m : ℝ)/2-m*Real.sqrt (2/15))/m := by
    field_simp
  rw [he]
  exact h

#print axioms actual_nuclear_off_diagonal_norm
#print axioms actual_nuclear_derivative_kernel_bound
#print axioms actual_nuclear_kernel_triangular_ratio
end NLA.RA08.Paper.LiteralJoins
