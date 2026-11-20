module

public import NLA.RA08.PaperSylvesterBound
public import NLA.RA08.PaperDiagonalCFC
public import NLA.RA08.PaperDerivativeScalar
public import NLA.RA08.PaperSpectralFrobeniusBound

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators Matrix.Norms.Frobenius
namespace NLA.RA08.Paper

theorem clippingDerivative_sylvester {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, b i ≠ 1) (E : RealMatrix n) :
    clippingDerivative b E=(1/2 : ℝ) • (E-diagonalSylvesterInverse (fun i => |b i-1|)
      ((Matrix.diagonal b-1)*E+E*(Matrix.diagonal b-1))) := by
  have hm : Matrix.diagonal b-1=Matrix.diagonal (fun i => b i-1) := by
    rw [← Matrix.diagonal_one,← Matrix.diagonal_sub]
  rw [hm]
  ext i j
  simp only [clippingDerivative,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,
    diagonalSylvesterInverse,Matrix.add_apply,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rw [clippingDividedDifference_absolute (b i) (b j) (hb i) (hb j)]
  ring

/-- The actual clipping function has a global quadratic remainder at any diagonal
    real base with no eigenvalue at its corner. The paper uses only PSD bases and
    sufficiently small nonnegative PSD perturbations, a special case. -/
theorem clipping_quadratic_remainder {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, b i ≠ 1) (E : RealMatrix n) (hE : E.IsHermitian) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      spectralNorm (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E) ≤ C*t^2 := by
  let B : RealMatrix n := Matrix.diagonal b
  let M : RealMatrix n := B-1
  let a : Fin n → ℝ := fun i => |b i-1|
  have hB : B.IsHermitian := by
    simp [B,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
  have hM : M.IsHermitian := hB.sub (Matrix.isHermitian_one)
  have ha : ∀ i, 0 < a i := fun i => abs_pos.mpr (sub_ne_zero.mpr (hb i))
  have hm : M=Matrix.diagonal (fun i => b i-1) := by
    dsimp [M,B]
    rw [← Matrix.diagonal_one,← Matrix.diagonal_sub]
  have h0 : matrixAbsolute M=Matrix.diagonal a := by
    rw [hm,matrixAbsolute_diagonal]
  obtain ⟨C,hC,hCt⟩ := sylvester_quadratic_remainder_bound a ha M E hM h0 hE
  obtain ⟨K,hK,hKA⟩ := spectralNorm_frobenius_bound n
  refine ⟨K*C/2,by positivity,?_⟩
  intro t
  have htH : (B+t • E).IsHermitian := hB.add (hE.smul (by simp [IsSelfAdjoint]))
  have hshift : B+t • E-1=M+t • E := by dsimp [M];abel
  have hi : functionalCalculus witnessFunction (B+t • E)-
      functionalCalculus witnessFunction B-t • clippingDerivative b E =
      -(1/2 : ℝ) • (matrixAbsolute (M+t • E)-Matrix.diagonal a-
        t • diagonalSylvesterInverse a (M*E+E*M)) := by
    rw [matrix_clipping_absolute (B+t • E) htH,matrix_clipping_absolute B hB,
      hshift,h0,clippingDerivative_sylvester b hb E]
    change (1/2 : ℝ) • (B+t • E+1-matrixAbsolute (M+t • E))-
      (1/2 : ℝ) • (B+1-Matrix.diagonal a)-
      t • ((1/2 : ℝ) • (E-diagonalSylvesterInverse a (M*E+E*M))) = _
    module
  change spectralNorm (functionalCalculus witnessFunction (B+t • E)-
      functionalCalculus witnessFunction B-t • clippingDerivative b E) ≤ _
  rw [hi]
  calc
    _ ≤ K*frobeniusNorm (-(1/2 : ℝ) • (matrixAbsolute (M+t • E)-Matrix.diagonal a-
        t • diagonalSylvesterInverse a (M*E+E*M))) := hKA _
    _ = (K/2)*frobeniusNorm (matrixAbsolute (M+t • E)-Matrix.diagonal a-
        t • diagonalSylvesterInverse a (M*E+E*M)) := by
      simp only [frobeniusNorm,norm_smul,Real.norm_eq_abs]
      norm_num
      ring
    _ ≤ (K/2)*(C*t^2) := mul_le_mul_of_nonneg_left (hCt t) (by positivity)
    _ = (K*C/2)*t^2 := by ring

#print axioms clipping_quadratic_remainder
end NLA.RA08.Paper
