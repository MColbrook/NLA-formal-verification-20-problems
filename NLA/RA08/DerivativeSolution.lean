module

public import NLA.RA08.PaperDerivativeStatement

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix Topology
namespace NLA.RA08.Paper

theorem paper_matrixAbsolute_frobenius_nonexpansive {n : ℕ} (A B : RealMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    frobeniusNorm (matrixAbsolute A-matrixAbsolute B) ≤ frobeniusNorm (A-B) := by
  exact matrixAbsolute_frobenius_nonexpansive A B hA hB

theorem paper_matrixAbsolute_square {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    matrixAbsolute A*matrixAbsolute A=A*A := by
  exact matrixAbsolute_square A hA

theorem paper_matrix_clipping_absolute {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    functionalCalculus witnessFunction A = (1/2 : ℝ) • (A+1-matrixAbsolute (A-1)) := by
  exact matrix_clipping_absolute A hA

theorem paper_clippingDividedDifference_absolute (x y : ℝ) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    clippingDividedDifference x y =
      (1/2 : ℝ)*(1-(x+y-2)/(|x-1|+|y-1|)) := by
  exact clippingDividedDifference_absolute x y hx1 hy1

theorem paper_spectralNorm_frobenius_bound (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ A : RealMatrix n, spectralNorm A ≤ K*frobeniusNorm A := by
  exact spectralNorm_frobenius_bound n

theorem paper_functionalCalculus_diagonal {n : ℕ} (f : ℝ → ℝ) (hf : Continuous f)
    (b : Fin n → ℝ) :
    functionalCalculus f (Matrix.diagonal b)=Matrix.diagonal (fun i => f (b i)) := by
  exact functionalCalculus_diagonal f hf b

theorem paper_sylvester_quadratic_remainder_bound {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (M E : RealMatrix n)
    (hM : M.IsHermitian) (h0 : matrixAbsolute M=Matrix.diagonal a)
    (hE : E.IsHermitian) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      frobeniusNorm (matrixAbsolute (M+t • E)-Matrix.diagonal a-
        t • diagonalSylvesterInverse a (M*E+E*M)) ≤ C*t^2 := by
  exact sylvester_quadratic_remainder_bound a ha M E hM h0 hE

theorem paper_clippingDerivative_sylvester {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, b i ≠ 1) (E : RealMatrix n) :
    clippingDerivative b E=(1/2 : ℝ) • (E-diagonalSylvesterInverse (fun i => |b i-1|)
      ((Matrix.diagonal b-1)*E+E*(Matrix.diagonal b-1))) := by
  exact clippingDerivative_sylvester b hb E

theorem paper_clipping_quadratic_remainder {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, b i ≠ 1) (E : RealMatrix n) (hE : E.IsHermitian) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      spectralNorm (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E) ≤ C*t^2 := by
  exact clipping_quadratic_remainder b hb E hE

theorem paper_threshold_derivative_spectral_bigO {n : ℕ} (b : Fin n → ℝ)
    (hb : ∀ i, b i ≠ 1) (E : RealMatrix n) (hE : E.IsHermitian) :
    (fun t : ℝ => Matrix.toEuclideanCLM (𝕜 := ℝ)
      (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun t : ℝ => t^2) := by
  exact threshold_derivative_spectral_bigO b hb E hE

theorem paper_threshold_derivative {n : ℕ} (b : Fin n → ℝ)
    (_hB : (Matrix.diagonal b).PosSemidef) (hb : ∀ i, b i ≠ 1)
    (E : RealMatrix n) (hE : E.IsHermitian) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      (Matrix.diagonal b+t • E).PosSemidef →
      spectralNorm (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E) ≤ C*t^2 := by
  exact threshold_derivative b _hB hb E hE

#print axioms NLA.RA08.Paper.paper_matrixAbsolute_frobenius_nonexpansive
#print axioms NLA.RA08.Paper.paper_matrixAbsolute_square
#print axioms NLA.RA08.Paper.paper_matrix_clipping_absolute
#print axioms NLA.RA08.Paper.paper_clippingDividedDifference_absolute
#print axioms NLA.RA08.Paper.paper_spectralNorm_frobenius_bound
#print axioms NLA.RA08.Paper.paper_functionalCalculus_diagonal
#print axioms NLA.RA08.Paper.paper_sylvester_quadratic_remainder_bound
#print axioms NLA.RA08.Paper.paper_clippingDerivative_sylvester
#print axioms NLA.RA08.Paper.paper_clipping_quadratic_remainder
#print axioms NLA.RA08.Paper.paper_threshold_derivative_spectral_bigO
#print axioms NLA.RA08.Paper.paper_threshold_derivative
end NLA.RA08.Paper
