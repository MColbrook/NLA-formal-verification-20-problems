module

public import NLA.RA08.PaperNuclearPolar
public import NLA.RA08.PaperNuclearVariational
public import NLA.RA08.PaperNuclearTriangularError

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclear_trace_cauchy_squared {m : ℕ} (R E : RealMatrix m) :
    ((R.transpose*E).trace)^2 ≤ frobeniusSquared R*frobeniusSquared E := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin m))
    (fun p => R p.1 p.2) (fun p => E p.1 p.2)
  have ht : (∑ p : Fin m × Fin m, R p.1 p.2*E p.1 p.2)=(R.transpose*E).trace := by
    simp only [Fintype.sum_prod_type,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply]
    exact Finset.sum_comm
  have hR : (∑ p : Fin m × Fin m, (R p.1 p.2)^2)=frobeniusSquared R := by
    simp only [frobeniusSquared,Fintype.sum_prod_type]
  have hE : (∑ p : Fin m × Fin m, (E p.1 p.2)^2)=frobeniusSquared E := by
    simp only [frobeniusSquared,Fintype.sum_prod_type]
  rwa [ht,hR,hE] at h

theorem nuclear_unitary_frobenius_squared {m : ℕ} (R : RealMatrix m)
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℝ) : frobeniusSquared R=m := by
  let U : Matrix.unitaryGroup (Fin m) ℝ := ⟨R,hR⟩
  rw [frobeniusSquared_trace,show R.transpose*R=1 from real_unitary_transpose_mul U]
  simp [Matrix.trace]

theorem nuclear_unitary_trace_abs {m : ℕ} (R : RealMatrix m)
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℝ) : |R.transpose.trace| ≤ m := by
  unfold Matrix.trace
  calc
    _ ≤ ∑ i : Fin m, |R.transpose i i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Matrix.transpose_apply,Real.norm_eq_abs] using entry_norm_bound_of_unitary hR i i
    _ = m := by simp

theorem nuclear_unitary_error_trace {m : ℕ} (R E : RealMatrix m)
    (hR : R ∈ Matrix.unitaryGroup (Fin m) ℝ)
    (hE : frobeniusSquared E ≤ 2*m/15) :
    |(R.transpose*E).trace| ≤ m*Real.sqrt (2/15) := by
  have h := nuclear_trace_cauchy_squared R E
  rw [nuclear_unitary_frobenius_squared R hR] at h
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hsq : |(R.transpose*E).trace|^2 ≤ ((m : ℝ)*Real.sqrt (2/15))^2 := by
    calc
      _ = ((R.transpose*E).trace)^2 := sq_abs _
      _ ≤ m*frobeniusSquared E := h
      _ ≤ m*(2*m/15) := mul_le_mul_of_nonneg_left hE hm
      _ = _ := by rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2/15)]; ring
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hsq

theorem nuclearKernel_polar_trace_lower (m : ℕ) :
    nuclearNorm (nuclearTriangular m)-(m : ℝ)/2-m*Real.sqrt (2/15) ≤
      ((nuclearTriangularPolar m).transpose*nuclearKernel m).trace := by
  let R := nuclearTriangularPolar m
  let E := nuclearKernel m-(nuclearTriangular m-(1/2 : ℝ) • (1 : RealMatrix m))
  have hR := nuclearTriangularPolar_unitary m
  have hE : frobeniusSquared E ≤ 2*m/15 := nuclearTriangular_error_frobenius_squared m
  have ht := nuclear_unitary_trace_abs R hR
  have he := nuclear_unitary_error_trace R E hR hE
  have ha := nuclearTriangularPolar_attains m
  have hlin : (R.transpose*E).trace=(R.transpose*nuclearKernel m).trace-
      ((R.transpose*nuclearTriangular m).trace-(1/2 : ℝ)*R.transpose.trace) := by
    dsimp only [E]
    rw [Matrix.mul_sub,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,
      Matrix.trace_sub,Matrix.trace_sub,Matrix.trace_smul]
    rfl
  have htl := le_abs_self R.transpose.trace
  have hel := neg_abs_le (R.transpose*E).trace
  change (R.transpose*nuclearTriangular m).trace=nuclearNorm (nuclearTriangular m) at ha
  change _ ≤ (R.transpose*nuclearKernel m).trace
  linarith

#print axioms nuclearKernel_polar_trace_lower
end NLA.RA08.Paper
