module

public import NLA.RA08.PaperNuclearLiftDerivative
public import NLA.RA08.PaperNuclearLiftTraceDefinitions
public import NLA.RA08.PaperNuclearBlockTrace

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearLiftUnitary_unitary {n : ℕ} (R : RealMatrix n)
    (hR : R ∈ Matrix.unitaryGroup (Fin n) ℝ) :
    nuclearLiftUnitary R ∈ Matrix.unitaryGroup (Fin (n+1)) ℝ := by
  let U : Matrix.unitaryGroup (Fin n) ℝ := ⟨R,hR⟩
  have hu : R.transpose*R=1 := real_unitary_transpose_mul U
  let B : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ :=
    Matrix.fromBlocks R 0 0 1
  have hB : B.transpose*B=1 := by
    simp only [B,Matrix.fromBlocks_transpose,Matrix.transpose_zero,Matrix.transpose_one,
      Matrix.fromBlocks_multiply,Matrix.zero_mul,Matrix.mul_zero,Matrix.one_mul,
      zero_add,add_zero,hu]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  unfold nuclearLiftUnitary
  change (B.submatrix _ _).transpose*B.submatrix _ _=1
  rw [Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,hB]
  simp

theorem nuclearLiftUnitary_trace {n : ℕ} (R : RealMatrix n) (G : RealMatrix (n+1)) :
    (nuclearLiftUnitary R*G).trace=
      (R*G.submatrix Fin.castSucc Fin.castSucc).trace+G (Fin.last n) (Fin.last n) := by
  simp [Matrix.trace,Matrix.diag,Matrix.mul_apply,Fin.sum_univ_castSucc,
    nuclearLiftUnitary,Matrix.submatrix_apply]

theorem nuclearLiftDerivative_trace (m : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    (nuclearLiftUnitary (functionalCalculus realSign (nuclearDerivative m))*
      nuclearLiftDerivative m η).trace=η*nuclearNorm (nuclearDerivative m)+1-η := by
  rw [nuclearLiftUnitary_trace,nuclearLiftDerivative_last m η hη1]
  have hp : (nuclearLiftDerivative m η).submatrix Fin.castSucc Fin.castSucc=
      η • nuclearDerivative m := by
    ext i j
    exact nuclearLiftDerivative_prefix m η hη0 i j
  rw [hp,Matrix.mul_smul,Matrix.trace_smul,cfc_realSign_attains _ (nuclearDerivative_isHermitian m)]
  simp only [smul_eq_mul]
  ring

theorem nuclearLiftDerivative_nuclear_lower (m : ℕ) (η : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    η*nuclearNorm (nuclearDerivative m)+1-η ≤ nuclearNorm (nuclearLiftDerivative m η) := by
  rw [← nuclearLiftDerivative_trace m η hη0 hη1]
  apply unitary_trace_le_nuclear
  · exact nuclearLiftUnitary_unitary _ (cfc_realSign_unitary _ (nuclearDerivative_isHermitian m))
  · exact nuclearLiftDerivative_isHermitian m η

theorem nuclearLiftOutput_lower (m : ℕ) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 0 ≤ t →
      t*(η*nuclearNorm (nuclearDerivative m)+1-η)-K*t^2 ≤
        nuclearNorm (nuclearLiftOutput m η t) := by
  obtain ⟨K,hK,hKt⟩ := nuclearLift_nuclear_remainder m η
  refine ⟨K,hK,?_⟩
  intro t ht
  have hG := nuclearLiftDerivative_isHermitian m η
  have hF := nuclearLiftOutput_isHermitian m η t
  have htG : (t • nuclearLiftDerivative m η).IsHermitian := hG.smul (by simp [IsSelfAdjoint])
  have htriangle := nuclearNorm_hermitian_sub (nuclearLiftOutput m η t)
    (nuclearLiftOutput m η t-t • nuclearLiftDerivative m η) hF (hF.sub htG)
  have hid : nuclearLiftOutput m η t-(nuclearLiftOutput m η t-t • nuclearLiftDerivative m η)=
      t • nuclearLiftDerivative m η := by abel
  rw [hid,nuclearNorm_hermitian_smul _ hG t,abs_of_nonneg ht] at htriangle
  have hlead := mul_le_mul_of_nonneg_left (nuclearLiftDerivative_nuclear_lower m η hη0 hη1) ht
  have herr := hKt t
  linarith

#print axioms nuclearLiftOutput_lower
end NLA.RA08.Paper
