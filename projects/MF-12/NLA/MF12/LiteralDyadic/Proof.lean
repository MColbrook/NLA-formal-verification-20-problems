module

public import NLA.MF12.LiteralDyadic.Definitions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace RootMF12LiteralDyadic
open NLA.MF12 NLA.MF12.Paper

theorem dyadic_integer (z : ℤ) : IsDyadic (z : ℝ) := ⟨z,0,by simp⟩
theorem dyadic_product {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x*y) := by
  obtain ⟨a,k,rfl⟩ := hx
  obtain ⟨b,l,rfl⟩ := hy
  exact ⟨a*b,k+l,by simp [pow_add,div_mul_div_comm]⟩

theorem actual_rational_parameters (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    2 ≤ b ∧ 0 < (a:ℝ)/(b:ℝ) ∧ (a:ℝ)/(b:ℝ) < 1 ∧
      0 < Real.rpow 2 (-(b:ℝ)) ∧ Real.rpow 2 (-(b:ℝ)) ≤ 1/4 ∧
      Real.rpow 2 (-((b-a:ℕ):ℝ)) =
        Real.rpow (Real.rpow 2 (-(b:ℝ))) (1-(a:ℝ)/(b:ℝ)) ∧
      IsDyadic (Real.rpow 2 (-(b:ℝ))) ∧ IsDyadic (Real.rpow 2 (-((b-a:ℕ):ℝ))) := by
  have hb : 2 ≤ b := by omega
  have hbR : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  refine ⟨hb,div_pos (by exact_mod_cast (show 0<a by omega)) hbR,
    (div_lt_one hbR).mpr (by exact_mod_cast hab),Real.rpow_pos_of_pos (by norm_num) _,?_,?_,?_,?_⟩
  · calc
      _ ≤ Real.rpow 2 (-2) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have hb2 : (2:ℝ) ≤ b := by exact_mod_cast hb
        linarith)
      _ = 1/4 := by norm_num [Real.rpow_neg,Real.rpow_two]
  · simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    rw [Nat.cast_sub hab.le]
    field_simp
  · refine ⟨1,b,?_⟩
    simp [Real.rpow_neg,Real.rpow_natCast]
  · refine ⟨1,b-a,?_⟩
    simp [Real.rpow_neg,Real.rpow_natCast]

theorem actual_parameter_entries_dyadic (lam mu : ℝ) (hlam : IsDyadic lam) (hmu : IsDyadic mu) :
    ∀ i j, IsDyadic (parameterMatrix lam mu i j) ∧ IsDyadic (resetMatrix i j) := by
  have h0 : IsDyadic (0:ℝ) := by simpa using dyadic_integer 0
  have h1 : IsDyadic (1:ℝ) := by simpa using dyadic_integer 1
  have hn : IsDyadic (-1:ℝ) := by simpa using dyadic_integer (-1)
  intro i j
  constructor
  · fin_cases i <;> fin_cases j <;> norm_num [parameterMatrix] <;> assumption
  · fin_cases i <;> fin_cases j <;>
      norm_num [resetMatrix,sourceU,sourceV,Matrix.mul_apply,Fin.sum_univ_succ] <;> assumption

theorem actual_tensor_dyadic {d e : ℕ} (A : Square d) (B : Square e)
    (hA : ∀ i j, IsDyadic (A i j)) (hB : ∀ i j, IsDyadic (B i j)) :
    ∀ i j, IsDyadic (tensor A B i j) := by
  intro i j
  exact dyadic_product (hA _ _) (hB _ _)

theorem actual_jordan_entries_dyadic (m : ℕ) : ∀ i j, IsDyadic (jordanMatrix m i j) := by
  intro i j
  simp only [jordanMatrix,upperShift,Matrix.add_apply,Matrix.one_apply]
  split_ifs <;> norm_num <;> first | simpa using dyadic_integer 0 | simpa using dyadic_integer 1 | simpa using dyadic_integer 2

#print axioms actual_rational_parameters
#print axioms actual_parameter_entries_dyadic
end RootMF12LiteralDyadic
