module

public import NLA.MD06.QuantitativeCorrection.Definitions
public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Spectral
open Reference.MD06Correction

def LaplacianOperator {n : ℕ} (G : SimpleGraph (Fin n)) : Configuration n →ₗ[ℝ] Configuration n := by
  classical
  exact (G.lapMatrix ℝ).toEuclideanLin

theorem LaplacianSymmetric {n : ℕ} (G : SimpleGraph (Fin n)) : (LaplacianOperator G).IsSymmetric := by
  classical
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (G.posSemidef_lapMatrix ℝ).isHermitian

def LaplacianEigenvalues {n : ℕ} (G : SimpleGraph (Fin n)) : Fin n → ℝ :=
  (LaplacianSymmetric G).eigenvalues (by simp [Configuration])

def LaplacianEigenbasis {n : ℕ} (G : SimpleGraph (Fin n)) : OrthonormalBasis (Fin n) ℝ (Configuration n) :=
  (LaplacianSymmetric G).eigenvectorBasis (by simp [Configuration])

def LaplacianGap {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 2 ≤ n) : ℝ :=
  LaplacianEigenvalues G ⟨n-2,by omega⟩
end Reference.MD06Spectral
