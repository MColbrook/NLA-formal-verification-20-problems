module

public import NLA.RA08.PaperNuclearAbsolute
public import NLA.RA08.PaperNuclearSignDefinitions
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators MatrixOrder
namespace NLA.RA08.Paper

theorem unitary_trace_le_nuclear {n : ℕ} (Q A : RealMatrix n)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℝ) (hA : A.IsHermitian) :
    (Q*A).trace ≤ nuclearNorm A := by
  let U := hA.eigenvectorUnitary
  let q : Matrix.unitaryGroup (Fin n) ℝ := ⟨Q,hQ⟩
  let R : RealMatrix n := (U : RealMatrix n).transpose*Q*(U : RealMatrix n)
  have hR : R ∈ Matrix.unitaryGroup (Fin n) ℝ := by
    have he : R=(star U*q*U : Matrix.unitaryGroup (Fin n) ℝ) := by
      simp only [R,q,Submonoid.coe_mul,Unitary.coe_star,Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [he]
    exact SetLike.coe_mem _
  have hid : functionalCalculus id A=A := cfc_id' ℝ A hA
  have hspec := real_cfc_spectral_form A hA id
  simp only [hid,id_eq] at hspec
  have ht : (Q*A).trace=∑ i, R i i*hA.eigenvalues i := by
    conv_lhs => rw [hspec]
    change (Q*((U : RealMatrix n)*Matrix.diagonal hA.eigenvalues*(U : RealMatrix n).transpose)).trace = _
    rw [← Matrix.mul_assoc,Matrix.trace_mul_cycle]
    rw [← Matrix.mul_assoc]
    change (R*Matrix.diagonal hA.eigenvalues).trace = _
    simp only [Matrix.trace,Matrix.diag,Matrix.mul_diagonal]
  rw [ht,nuclearNorm_hermitian_spectral A hA]
  apply Finset.sum_le_sum
  intro i _
  have hb : |R i i| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using entry_norm_bound_of_unitary hR i i
  calc
    _ ≤ |R i i*hA.eigenvalues i| := le_abs_self _
    _ = |R i i| * |hA.eigenvalues i| := abs_mul _ _
    _ ≤ 1*|hA.eigenvalues i| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)
    _ = _ := one_mul _

theorem realSign_square (x : ℝ) : realSign x*realSign x=1 := by
  unfold realSign
  split_ifs <;> norm_num

theorem realSign_mul (x : ℝ) : realSign x*x=|x| := by
  unfold realSign
  split_ifs with hx
  · rw [abs_of_nonneg hx,one_mul]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    ring

theorem cfc_realSign_unitary {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    functionalCalculus realSign A ∈ Matrix.unitaryGroup (Fin n) ℝ := by
  let U := hA.eigenvectorUnitary
  have hdiag : Matrix.diagonal (fun i => realSign (hA.eigenvalues i))*
      Matrix.diagonal (fun i => realSign (hA.eigenvalues i))=(1 : RealMatrix n) := by
    rw [Matrix.diagonal_mul_diagonal]
    simp only [realSign_square,Matrix.diagonal_one]
  have hH : (functionalCalculus realSign A).IsHermitian := cfc_predicate realSign A
  rw [Matrix.mem_unitaryGroup_iff',hH.star_eq]
  rw [real_cfc_spectral_form A hA realSign]
  change ((U : RealMatrix n)*Matrix.diagonal (fun i => realSign (hA.eigenvalues i))*(U : RealMatrix n).transpose)*
    ((U : RealMatrix n)*Matrix.diagonal (fun i => realSign (hA.eigenvalues i))*(U : RealMatrix n).transpose)=1
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : RealMatrix n).transpose (U : RealMatrix n),real_unitary_transpose_mul,Matrix.one_mul]
  rw [← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _),hdiag,Matrix.one_mul,
    real_unitary_mul_transpose]

theorem cfc_realSign_attains {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian) :
    (functionalCalculus realSign A*A).trace=nuclearNorm A := by
  have hm : functionalCalculus realSign A*A=matrixAbsolute A := by
    have hid : cfc (fun x : ℝ => x) A=A := cfc_id' ℝ A hA
    have hc : ContinuousOn realSign (spectrum ℝ A) := by
      rw [continuousOn_iff_continuous_domRestrict]
      fun_prop
    have hmul := cfc_mul realSign (fun x : ℝ => x) A hc continuous_id.continuousOn
    have he : (fun x : ℝ => realSign x*x)=abs := funext realSign_mul
    rw [he,hid] at hmul
    exact hmul.symm
  rw [hm,nuclearNorm_hermitian A hA]

theorem nuclearNorm_hermitian_triangle {n : ℕ} (A B : RealMatrix n)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    nuclearNorm (A+B) ≤ nuclearNorm A+nuclearNorm B := by
  let Q := functionalCalculus realSign (A+B)
  have hQ := cfc_realSign_unitary (A+B) (hA.add hB)
  have hEq := cfc_realSign_attains (A+B) (hA.add hB)
  rw [← hEq,Matrix.mul_add,Matrix.trace_add]
  exact add_le_add (unitary_trace_le_nuclear Q A hQ hA) (unitary_trace_le_nuclear Q B hQ hB)

#print axioms nuclearNorm_hermitian_triangle
end NLA.RA08.Paper
