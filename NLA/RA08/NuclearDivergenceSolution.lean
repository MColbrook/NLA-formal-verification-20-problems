module

public import NLA.RA08.PaperNuclearDivergence

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem paper_nuclearDifferenceEigenvalue_pos {m : ℕ} (j : Fin m) :
    0 < nuclearDifferenceEigenvalue j := by
  exact nuclearDifferenceEigenvalue_pos j

theorem paper_nuclearTriangular_gram_inverse (m : ℕ) :
    ((nuclearDifference m).transpose*nuclearDifference m)*
      ((nuclearTriangular m).transpose*nuclearTriangular m)=1 := by
  exact nuclearTriangular_gram_inverse m

theorem paper_nuclearTriangular_sine_eigenvector {m : ℕ} (j : Fin m) :
    ((nuclearTriangular m).transpose*nuclearTriangular m) *ᵥ nuclearSineVector j =
      (nuclearDifferenceEigenvalue j)⁻¹ • nuclearSineVector j := by
  exact nuclearTriangular_sine_eigenvector j

theorem paper_nuclearTriangular_spectrum_permutation (m : ℕ) (hG : (nuclearTriangularGram m).PosSemidef) :
    ∃ e : Fin m ≃ Fin m, ∀ j,
      hG.isHermitian.eigenvalues (e j)=
        (nuclearDifferenceEigenvalue j)⁻¹ := by
  exact nuclearTriangular_spectrum_permutation m

theorem paper_nuclearTriangular_nuclearNorm (m : ℕ) :
    nuclearNorm (nuclearTriangular m)=
      ∑ j : Fin m, 1/(2*Real.sin (nuclearSineAngle j/2)) := by
  exact nuclearTriangular_nuclearNorm m

theorem paper_nuclearTriangular_singular_lower {m : ℕ} (hm : 1 ≤ m) (j : Fin m) :
    1/(Real.pi*((j.val+1 : ℕ) : ℝ)) ≤
      (1/(2*Real.sin (nuclearSineAngle j/2)))/(m : ℝ) := by
  exact nuclearTriangular_singular_lower hm j

theorem paper_nuclearTriangular_nuclearNorm_lower (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m+1)/Real.pi ≤ nuclearNorm (nuclearTriangular m)/(m : ℝ) := by
  exact nuclearTriangular_nuclearNorm_lower m hm

theorem paper_nuclearTriangularGram_spectrum_pos (m : ℕ) (x : ℝ)
    (hx : x ∈ spectrum ℝ (nuclearTriangularGram m)) : 0 < x := by
  exact nuclearTriangularGram_spectrum_pos m x hx

theorem paper_nuclearTriangularPolar_unitary (m : ℕ) :
    nuclearTriangularPolar m ∈ Matrix.unitaryGroup (Fin m) ℝ := by
  exact nuclearTriangularPolar_unitary m

theorem paper_nuclearTriangularPolar_attains (m : ℕ) :
    ((nuclearTriangularPolar m).transpose*nuclearTriangular m).trace=
      nuclearNorm (nuclearTriangular m) := by
  exact nuclearTriangularPolar_attains m

theorem paper_nuclear_trace_cauchy_squared {m : ℕ} (R E : RealMatrix m) :
    ((R.transpose*E).trace)^2 ≤ frobeniusSquared R*frobeniusSquared E := by
  exact nuclear_trace_cauchy_squared R E

theorem paper_nuclear_unitary_frobenius_squared {m : ℕ} (R : RealMatrix m)
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℝ) : frobeniusSquared R=m := by
  exact nuclear_unitary_frobenius_squared R hR

theorem paper_nuclear_unitary_trace_abs {m : ℕ} (R : RealMatrix m)
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℝ) : |R.transpose.trace| ≤ m := by
  exact nuclear_unitary_trace_abs R hR

theorem paper_nuclear_unitary_error_trace {m : ℕ} (R E : RealMatrix m)
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℝ)
    (hE : frobeniusSquared E ≤ 2*m/15) :
    |(R.transpose*E).trace| ≤ m*Real.sqrt (2/15) := by
  exact nuclear_unitary_error_trace R E hR hE

theorem paper_nuclearKernel_polar_trace_lower (m : ℕ) :
    nuclearNorm (nuclearTriangular m)-(m : ℝ)/2-m*Real.sqrt (2/15) ≤
      ((nuclearTriangularPolar m).transpose*nuclearKernel m).trace := by
  exact nuclearKernel_polar_trace_lower m

theorem paper_nuclearBlockUnitary_unitary {m : ℕ} (R : RealMatrix m)
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℝ) :
    nuclearBlockUnitary R ∈ Matrix.unitaryGroup (Fin (m+m)) ℝ := by
  exact nuclearBlockUnitary_unitary R hR

theorem paper_nuclearDerivative_isHermitian (m : ℕ) : (nuclearDerivative m).IsHermitian := by
  exact nuclearDerivative_isHermitian m

theorem paper_nuclearDerivative_block_trace (m : ℕ) (hm : 1 ≤ m) (R : RealMatrix m) :
    (nuclearBlockUnitary R*nuclearDerivative m).trace=(R.transpose*nuclearKernel m).trace/m := by
  exact nuclearDerivative_block_trace m hm R

theorem paper_nuclearDerivative_trace_lower (m : ℕ) (hm : 1 ≤ m) (R : RealMatrix m)
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℝ) :
    (R.transpose*nuclearKernel m).trace/m ≤ nuclearNorm (nuclearDerivative m) := by
  exact nuclearDerivative_trace_lower m hm R hR

theorem paper_nuclearDerivative_lower (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m+1)/Real.pi-1/2-Real.sqrt (2/15) ≤ nuclearNorm (nuclearDerivative m) := by
  exact nuclearDerivative_lower m hm

theorem paper_nuclearDerivative_unbounded (C : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ C < nuclearNorm (nuclearDerivative m) := by
  exact nuclearDerivative_unbounded C

#print axioms NLA.RA08.Paper.paper_nuclearDifferenceEigenvalue_pos
#print axioms NLA.RA08.Paper.paper_nuclearTriangular_gram_inverse
#print axioms NLA.RA08.Paper.paper_nuclearTriangular_sine_eigenvector
#print axioms NLA.RA08.Paper.paper_nuclearTriangular_spectrum_permutation
#print axioms NLA.RA08.Paper.paper_nuclearTriangular_nuclearNorm
#print axioms NLA.RA08.Paper.paper_nuclearTriangular_singular_lower
#print axioms NLA.RA08.Paper.paper_nuclearTriangular_nuclearNorm_lower
#print axioms NLA.RA08.Paper.paper_nuclearTriangularGram_spectrum_pos
#print axioms NLA.RA08.Paper.paper_nuclearTriangularPolar_unitary
#print axioms NLA.RA08.Paper.paper_nuclearTriangularPolar_attains
#print axioms NLA.RA08.Paper.paper_nuclear_trace_cauchy_squared
#print axioms NLA.RA08.Paper.paper_nuclear_unitary_frobenius_squared
#print axioms NLA.RA08.Paper.paper_nuclear_unitary_trace_abs
#print axioms NLA.RA08.Paper.paper_nuclear_unitary_error_trace
#print axioms NLA.RA08.Paper.paper_nuclearKernel_polar_trace_lower
#print axioms NLA.RA08.Paper.paper_nuclearBlockUnitary_unitary
#print axioms NLA.RA08.Paper.paper_nuclearDerivative_isHermitian
#print axioms NLA.RA08.Paper.paper_nuclearDerivative_block_trace
#print axioms NLA.RA08.Paper.paper_nuclearDerivative_trace_lower
#print axioms NLA.RA08.Paper.paper_nuclearDerivative_lower
#print axioms NLA.RA08.Paper.paper_nuclearDerivative_unbounded
end NLA.RA08.Paper
