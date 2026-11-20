module

public import NLA.MF12.PaperSharpNorms
public import NLA.MF12.Lower

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.MF12.Paper

theorem mul_sourceV_entry_sharp (B : Square 6) :
    (B*sourceV) 0 1 ≤ Real.sqrt 2*spectralNorm B := by
  let x : EuclideanVector 6 := WithLp.toLp 2 ![0,0,0,0,1,1]
  let T := Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℝ) B
  have hx : ‖x‖ = Real.sqrt 2 := by
    have hs : ‖x‖^2 = 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [x, Fin.sum_univ_succ]
    have hp := norm_nonneg x
    have he := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    have hepos := Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have he : (B*sourceV) 0 1 = (T x) 0 := by
    simp [T, x, Matrix.mul_apply, Matrix.mulVec, dotProduct, sourceV, Fin.sum_univ_succ]
  calc
    _ ≤ |(B*sourceV) 0 1| := le_abs_self _
    _ = ‖(T x) 0‖ := by rw [he, Real.norm_eq_abs]
    _ ≤ ‖T x‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖*‖x‖ := T.le_opNorm x
    _ = Real.sqrt 2*spectralNorm B := by rw [hx]; exact mul_comm _ _

theorem parameter_reset_repeat_mul_V (lam μ : ℝ) (q k : ℕ) :
    (resetMatrix*parameterMatrix lam μ^q)^k*sourceV =
      sourceV*parameterCompressed lam μ q^k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, pow_succ']
      simp only [resetMatrix, parameterCompressed, Matrix.mul_assoc]

theorem parameter_padded_repeat_entry (lam μ : ℝ) (q k r : ℕ) :
    ((parameterMatrix lam μ^r*(resetMatrix*parameterMatrix lam μ^q)^k)*sourceV) 0 1 =
      (parameterCompressed lam μ q^k) 0 1 := by
  have hfirst (j : Fin 2) : (parameterMatrix lam μ^r*sourceV) 0 j = if j=0 then 1 else 0 := by
    rw [parameter_power]
    fin_cases j <;> norm_num [parameterPower, sourceV, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [Matrix.mul_assoc, parameter_reset_repeat_mul_V, ← Matrix.mul_assoc,
    Matrix.mul_apply, Fin.sum_univ_two, hfirst, hfirst]
  norm_num

theorem parameter_repeat_rayleigh (lam μ : ℝ) (q k r : ℕ) (hell : parameterLoss lam q ≠ 0) :
    (parameterGain μ q/parameterLoss lam q)*(1-(1-parameterLoss lam q)^k) ≤
      Real.sqrt 2*spectralNorm (parameterMatrix lam μ^r*(resetMatrix*parameterMatrix lam μ^q)^k) := by
  have h := mul_sourceV_entry_sharp (parameterMatrix lam μ^r*(resetMatrix*parameterMatrix lam μ^q)^k)
  rw [parameter_padded_repeat_entry, parameter_compressed_powers,
    triangular_geometric_power _ _ hell] at h
  exact h

theorem parameter_repeat_word (lam μ : ℝ) (q n : ℕ) :
    ∃ w : List Bool, w.length = n ∧
      binaryProduct (parameterMatrix lam μ) resetMatrix w =
        parameterMatrix lam μ^(n-n/(q+1)*(q+1)) *
          (resetMatrix*parameterMatrix lam μ^q)^(n/(q+1)) := by
  let k := n/(q+1)
  let r := n-k*(q+1)
  refine ⟨(List.replicate k (List.replicate q false ++ [true])).flatten ++
    List.replicate r false, ?_, ?_⟩
  · have hr : r+k*(q+1) = n := Nat.sub_add_cancel (Nat.div_mul_le_self n (q+1))
    simpa [List.length_flatten, add_comm] using hr
  · rw [binaryProduct_append, binaryProduct_replicate_false,
      binaryProduct_flatten_replicate, binaryProduct_append, binaryProduct_replicate_false]
    simp [binaryProduct_cons, r, k]

theorem parameter_power_norm_ge_one (lam μ : ℝ) (n : ℕ) :
    1 ≤ spectralNorm (parameterMatrix lam μ^n) := by
  have h := abs_entry_le_spectralNorm (parameterMatrix lam μ^n) 0 0
  rw [parameter_power] at h ⊢
  simpa [parameterPower] using h

#print axioms parameter_repeat_rayleigh
#print axioms parameter_repeat_word
end NLA.MF12.Paper
