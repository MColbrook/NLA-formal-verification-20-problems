module

public import NLA.RA08.LiteralJoins.Dilation
public import NLA.RA08.PaperNuclearHomogeneity
public import NLA.RA08.PaperNuclearPSD

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper.LiteralJoins

theorem symmetricDilation_add {m : ℕ} (A B : RealMatrix m) :
    symmetricDilation (A+B)=symmetricDilation A+symmetricDilation B := by
  ext i k
  simp only [symmetricDilation,Matrix.submatrix_apply,Matrix.add_apply]
  cases hi : (finSumFinEquiv (m := m) (n := m)).symm i <;>
    cases hk : (finSumFinEquiv (m := m) (n := m)).symm k <;> simp [Matrix.fromBlocks]

theorem symmetricDilation_smul {m : ℕ} (c : ℝ) (A : RealMatrix m) :
    symmetricDilation (c • A)=c • symmetricDilation A := by
  ext i k
  simp only [symmetricDilation,Matrix.submatrix_apply,Matrix.smul_apply]
  cases hi : (finSumFinEquiv (m := m) (n := m)).symm i <;>
    cases hk : (finSumFinEquiv (m := m) (n := m)).symm k <;> simp [Matrix.fromBlocks]

theorem nuclearNorm_triangle {m : ℕ} (A B : RealMatrix m) :
    nuclearNorm (A+B) ≤ nuclearNorm A+nuclearNorm B := by
  have h := nuclearNorm_hermitian_triangle (symmetricDilation A) (symmetricDilation B)
    (symmetricDilation_hermitian A) (symmetricDilation_hermitian B)
  rw [← symmetricDilation_add,symmetricDilation_nuclearNorm,
    symmetricDilation_nuclearNorm,symmetricDilation_nuclearNorm] at h
  linarith

theorem nuclearNorm_smul {m : ℕ} (c : ℝ) (A : RealMatrix m) :
    nuclearNorm (c • A)=|c| *nuclearNorm A := by
  have h := nuclearNorm_hermitian_smul (symmetricDilation A) (symmetricDilation_hermitian A) c
  rw [← symmetricDilation_smul,symmetricDilation_nuclearNorm,symmetricDilation_nuclearNorm] at h
  linarith

theorem nuclearNorm_neg {m : ℕ} (A : RealMatrix m) : nuclearNorm (-A)=nuclearNorm A := by
  simpa using nuclearNorm_smul (-1) A

theorem nuclearNorm_sub {m : ℕ} (A B : RealMatrix m) :
    nuclearNorm (A-B) ≤ nuclearNorm A+nuclearNorm B := by
  simpa only [sub_eq_add_neg,nuclearNorm_neg] using nuclearNorm_triangle A (-B)

theorem nuclearNorm_one (m : ℕ) : nuclearNorm (1 : RealMatrix m)=m := by
  rw [nuclearNorm_posSemidef _ Matrix.PosSemidef.one]
  simp [Matrix.trace]

#print axioms nuclearNorm_triangle
#print axioms nuclearNorm_smul
end NLA.RA08.Paper.LiteralJoins
