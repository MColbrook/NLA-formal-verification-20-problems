module

public import Mathlib.Analysis.SpecificLimits.Normed
public import NLA.TR27.PaperTensorRootFilter
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped Topology
open Filter
namespace NLA.TR27.Paper

/-- The printed linear-times-exponential upper bound is eventually smaller
than r^k for every fixed D and r>2. This lemma alone does not prove a rank bound. -/
theorem eventual_power_bound (D r : ℕ) (hr : 2 < r) :
    ∀ᶠ k : ℕ in atTop, (k*(D-1)+1)*2^k < r^k := by
  have hq : (1 : ℝ) < (r : ℝ)/2 := by
    have h : (2 : ℝ) < r := by exact_mod_cast hr
    linarith
  have h₁ := tendsto_pow_const_div_const_pow_of_one_lt 1 hq
  have h₀ := tendsto_pow_const_div_const_pow_of_one_lt 0 hq
  have hlim := (h₁.const_mul (((D-1 : ℕ) : ℝ))).add h₀
  have he : ∀ᶠ k : ℕ in atTop,
      (((D-1 : ℕ) : ℝ))*((k : ℝ)^1/((r : ℝ)/2)^k) + (k : ℝ)^0/((r : ℝ)/2)^k < 1 := by
    apply hlim.eventually (p := fun x : ℝ => x < 1)
    simp only [mul_zero, add_zero]
    exact Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)
  filter_upwards [he] with k hk
  have hpos : (0 : ℝ) < ((r : ℝ)/2)^k := by positivity
  have hfrac : (((k : ℝ)*((D-1 : ℕ) : ℝ)+1)/((r : ℝ)/2)^k) < 1 := by
    convert hk using 1 <;> ring
  have hlt := (div_lt_one hpos).mp hfrac
  rw [div_pow] at hlt
  have hfinal := (lt_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ)^k)).mp hlt
  exact_mod_cast hfinal

theorem explicit_thirteenth_power_saving_bound :
    (13*(12-1)+1)*2^13 < (3 : ℕ)^13 := by norm_num

#print axioms eventual_power_bound
#print axioms polynomial_tensor_root_average
#print axioms explicit_thirteenth_power_saving_bound
end NLA.TR27.Paper
