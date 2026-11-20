module

public import NLA.RA02.PaperBestScaling
public import NLA.RA02.PaperLUNonnegative

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem real_smul_matrix_zero_iff {m n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℂ) : c • A=0 ↔ A=0 := by
  constructor
  · intro hz
    have he := congrArg (fun B : Matrix (Fin m) (Fin n) ℂ => (c⁻¹ : ℝ) • B) hz
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul,smul_zero] using he
  · rintro rfl
    exact smul_zero c

theorem lu_pivotResidual_real_smul {m n : ℕ} (c : ℝ) (A : Matrix (Fin m) (Fin n) ℂ)
    (p : Fin m × Fin n) : NLA.RA03.pivotResidual (c • A) p=c • NLA.RA03.pivotResidual A p := by
  by_cases hc : c=0
  · subst c
    simp [NLA.RA03.pivotResidual]
  · have hcc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
    have hz : (c • A) p.1 p.2=0 ↔ A p.1 p.2=0 := by
      simp only [Matrix.smul_apply,Complex.real_smul,mul_eq_zero,hcc,false_or]
    by_cases hp : A p.1 p.2=0
    · rw [NLA.RA03.pivotResidual,if_pos (hz.mpr hp),NLA.RA03.pivotResidual,if_pos hp]
    · have hcp : (c • A) p.1 p.2 ≠ 0 := fun h => hp (hz.mp h)
      rw [NLA.RA03.pivotResidual,if_neg hcp,NLA.RA03.pivotResidual,if_neg hp]
      ext i j
      simp only [Matrix.smul_apply,Complex.real_smul]
      field_simp [hcc,hp]

theorem lu_pivotMass_real_smul {m n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (A : Matrix (Fin m) (Fin n) ℂ) (p : NLA.RA03.Pivot m n) :
    NLA.RA03.pivotMass (c • A) p=NLA.RA03.pivotMass A p := by
  have hz := real_smul_matrix_zero_iff c hc A
  by_cases hA : A=0
  · subst A
    rw [smul_zero]
  · have hC : c • A ≠ 0 := fun h => hA (hz.mp h)
    cases p with
    | none => simp only [NLA.RA03.pivotMass,if_neg hC,if_neg hA]
    | some ij =>
      simp only [NLA.RA03.pivotMass,if_neg hC,if_neg hA,frobenius_real_smul,
        Matrix.smul_apply,Complex.real_smul,Complex.normSq_mul,Complex.normSq_ofReal,pow_two]
      have hf : NLA.RA03.frobeniusSq A ≠ 0 := fun h => hA ((lu_frobeniusSq_eq_zero_iff A).mp h)
      field_simp [hc,hf]

theorem lu_expectedError_real_smul {m n : ℕ} (c : ℝ) (A : Matrix (Fin m) (Fin n) ℂ)
    (r : ℕ) : NLA.RA03.expectedError (c • A) r=c^2*NLA.RA03.expectedError A r := by
  by_cases hc : c=0
  · subst c
    rw [zero_smul,lu_expectedError_zero_matrix]
    simp
  · induction r generalizing A with
    | zero => rw [lu_expectedError_zero,lu_expectedError_zero,frobenius_real_smul]
    | succ r ih =>
      rw [lu_expectedError_succ,lu_expectedError_succ,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [lu_pivotMass_real_smul c hc]
      have hn : NLA.RA03.nextResidual (c • A) p=c • NLA.RA03.nextResidual A p := by
        cases p with
        | none => simp only [NLA.RA03.nextResidual,smul_zero]
        | some ij => exact lu_pivotResidual_real_smul c A ij
      rw [hn,ih]
      ring

#print axioms lu_expectedError_real_smul
end NLA.RA02.Paper
