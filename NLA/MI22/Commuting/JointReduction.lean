module

public import NLA.MI22.Commuting.EigenAction

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Unitary
namespace NLA.MI22.Commuting

theorem matrix_eq_of_joint_eigenvectors {n : ℕ} (A B X Y : Mat n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : Commute A B)
    (h : ∀ (v : Fin n → ℂ) (a b : ℝ),
      A *ᵥ v = (a : ℂ) • v → B *ᵥ v = (b : ℂ) • v → X *ᵥ v = Y *ᵥ v) : X = Y := by
  letI := InnerProductSpace.rclikeToReal ℂ (EuclideanSpace ℂ (Fin n))
  let AR := (Matrix.toEuclideanLin A).restrictScalars ℝ
  let BR := (Matrix.toEuclideanLin B).restrictScalars ℝ
  let ZR := (Matrix.toEuclideanLin (X - Y)).restrictScalars ℝ
  have ha : AR.IsSymmetric := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).restrictScalars
  have hb : BR.IsSymmetric := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).restrictScalars
  have hab : Commute AR BR := by
    ext v i
    change (A *ᵥ (B *ᵥ (WithLp.ofLp v))) i = (B *ᵥ (A *ᵥ (WithLp.ofLp v))) i
    rw [mulVec_mulVec, mulVec_mulVec, hAB.eq]
  have hspan := ha.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hb hab
  have hk : (⊤ : Submodule ℝ (EuclideanSpace ℂ (Fin n))) ≤ LinearMap.ker ZR := by
    rw [← hspan]
    refine iSup_le fun a => iSup_le fun b => ?_
    intro v hv
    have hva := Module.End.mem_eigenspace_iff.mp hv.1
    have hvb := Module.End.mem_eigenspace_iff.mp hv.2
    have h1 : A *ᵥ (WithLp.ofLp v) = (a : ℂ) • WithLp.ofLp v := by
      ext i
      simpa only [AR, Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp, LinearMap.restrictScalars_apply,
        WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul] using congrArg (fun z => (WithLp.ofLp z) i) hva
    have h2 : B *ᵥ (WithLp.ofLp v) = (b : ℂ) • WithLp.ofLp v := by
      ext i
      simpa only [BR, Matrix.toEuclideanLin, Matrix.toLpLin_apply, WithLp.ofLp_toLp, LinearMap.restrictScalars_apply,
        WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul] using congrArg (fun z => (WithLp.ofLp z) i) hvb
    have hh := h (WithLp.ofLp v) a b h1 h2
    change Matrix.toEuclideanLin (X-Y) v = 0
    apply WithLp.ofLp_injective
    change (X-Y) *ᵥ (WithLp.ofLp v) = 0
    rw [Matrix.sub_mulVec, hh, sub_self]
  have hz : ZR = 0 := LinearMap.ker_eq_top.mp (top_le_iff.mp hk)
  have hm : Matrix.toEuclideanLin (X-Y) = 0 := by
    ext v i
    exact congrArg (fun f : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n) => (f v) i) hz
  have : X-Y = 0 := Matrix.toEuclideanLin.injective (by simpa using hm)
  exact sub_eq_zero.mp this

#print axioms matrix_eq_of_joint_eigenvectors
end NLA.MI22.Commuting
