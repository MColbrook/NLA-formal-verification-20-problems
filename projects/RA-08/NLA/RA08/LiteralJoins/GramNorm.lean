module

public import NLA.RA08.PaperDiagonalCFC
public import NLA.RA08.PaperNuclearFrobenius
public import NLA.RA08.LiteralJoins.RealSVD.SVD

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper.LiteralJoins

theorem functionalCalculus_unitary_conjugate {n : ℕ}
    (A : RealMatrix n) (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : Continuous f)
    (U : Matrix.unitaryGroup (Fin n) ℝ) :
    functionalCalculus f ((U : RealMatrix n)*A*(U : RealMatrix n).transpose) =
      (U : RealMatrix n)*functionalCalculus f A*(U : RealMatrix n).transpose := by
  let φ : RealMatrix n ≃⋆ₐ[ℝ] RealMatrix n := Unitary.conjStarAlgAut ℝ (RealMatrix n) U
  have hφ : Continuous φ := φ.toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hUA : ((U : RealMatrix n)*A*(U : RealMatrix n).transpose).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : RealMatrix n) hA
  have hc := StarAlgHomClass.map_cfc (S := ℝ) (R := ℝ) φ f A hf.continuousOn hφ hA (by
    simpa only [φ,Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hUA.isSelfAdjoint)
  simpa only [functionalCalculus,φ,Unitary.conjStarAlgAut_apply,Unitary.coe_star,
    Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using hc.symm

theorem nuclearNorm_of_gram_diagonal {n : ℕ} (A : RealMatrix n)
    (U : Matrix.unitaryGroup (Fin n) ℝ) (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hG : A.transpose*A = (U : RealMatrix n)*Matrix.diagonal (fun i => (s i)^2)*
      (U : RealMatrix n).transpose) : nuclearNorm A = ∑ i, s i := by
  have hd : (Matrix.diagonal (fun i => (s i)^2)).IsHermitian := by
    simp [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [nuclearNorm,hG,functionalCalculus_unitary_conjugate _ hd Real.sqrt Real.continuous_sqrt U,
    functionalCalculus_diagonal Real.sqrt Real.continuous_sqrt,
    Matrix.trace_mul_cycle,real_unitary_transpose_mul,Matrix.one_mul,Matrix.trace_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  exact Real.sqrt_sq (hs i)

theorem nuclearNorm_of_svd {n : ℕ} (A U V : RealMatrix n)
    (hU : Reference.RealSVDPackage.IsOrthogonal U)
    (hV : Reference.RealSVDPackage.IsOrthogonal V)
    (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hA : A=U*Matrix.diagonal s*V.transpose) : nuclearNorm A = ∑ i, s i := by
  have hVu : V ∈ Matrix.unitaryGroup (Fin n) ℝ := by
    rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hV.1
  apply nuclearNorm_of_gram_diagonal A ⟨V,hVu⟩ s hs
  rw [hA]
  simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.diagonal_transpose]
  calc
    _ = V*Matrix.diagonal s*(U.transpose*U)*Matrix.diagonal s*V.transpose := by
      simp only [Matrix.mul_assoc]
    _ = V*Matrix.diagonal (fun i => (s i)^2)*V.transpose := by
      rw [hU.1,Matrix.mul_one,Matrix.mul_assoc V,Matrix.diagonal_mul_diagonal]
      simp only [pow_two]

theorem nuclearNorm_singular_values {n : ℕ} (A : RealMatrix n) :
    nuclearNorm A = ∑ i : Fin n, Reference.RealSVDPackage.singularValue A i.val := by
  obtain ⟨U,V,hU,hV,hA⟩ := Reference.RealSVDPackage.full_svd A
  exact nuclearNorm_of_svd A U V hU hV _
    (fun i => (Reference.RealSVDPackage.singular_values_semantics A).1 i.val) hA

#print axioms nuclearNorm_singular_values
end NLA.RA08.Paper.LiteralJoins
