module

public import NLA.TR04.FixedSharp.RatioLimit

@[expose] public section

set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology

namespace NLA.TR04.AllOrderSharp

/-- Distinct positive branch weights, all tending to one. The strict ordering
removes every truncation ambiguity in the sharpness construction. -/
def coefficient (n i : ℕ) : ℝ :=
  1 + (NLA.TR04.FixedSharp.sharpGamma n - 1) / ((i : ℝ) + 1)

theorem coefficient_pos (n i : ℕ) : 0 < coefficient n i := by
  have h := NLA.TR04.FixedSharp.sharpGamma_bounds n
  have hi : 0 < (i : ℝ) + 1 := by positivity
  unfold coefficient
  have hp : 0 < (NLA.TR04.FixedSharp.sharpGamma n - 1) / ((i : ℝ) + 1) :=
    div_pos (by linarith) hi
  linarith

theorem coefficient_strictAnti (n : ℕ) : StrictAnti (coefficient n) := by
  intro i j hij
  have h := NLA.TR04.FixedSharp.sharpGamma_bounds n
  have hi : 0 < (i : ℝ) + 1 := by positivity
  have hj : 0 < (j : ℝ) + 1 := by positivity
  have hij' : (i : ℝ) + 1 < (j : ℝ) + 1 := by exact_mod_cast Nat.add_lt_add_right hij 1
  unfold coefficient
  have hd : (NLA.TR04.FixedSharp.sharpGamma n - 1) / ((j : ℝ) + 1) <
      (NLA.TR04.FixedSharp.sharpGamma n - 1) / ((i : ℝ) + 1) := by
    rw [div_lt_div_iff₀ hj hi]
    exact mul_lt_mul_of_pos_left hij' (by linarith)
  linarith

theorem coefficient_sq_strictAnti (n : ℕ) :
    StrictAnti (fun i => coefficient n i ^ 2) := by
  intro i j hij
  have h := coefficient_strictAnti n hij
  have hi := coefficient_pos n i
  have hj := coefficient_pos n j
  nlinarith

theorem coefficient_tendsto_one (i : ℕ) :
    Tendsto (fun n => coefficient n i) atTop (𝓝 1) := by
  have h := ((NLA.TR04.FixedSharp.sharpGamma_tendsto_one.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))).div_const
      ((i : ℝ) + 1))
  have h' := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add h
  simpa only [sub_self, zero_div, add_zero, coefficient] using h'

def squaredErrorRatio (q n : ℕ) : ℝ :=
  (∑ i : Fin (q+1), coefficient n (i.val+1) ^ 2) / coefficient n 1 ^ 2

theorem squaredErrorRatio_tendsto (q : ℕ) :
    Tendsto (squaredErrorRatio q) atTop (𝓝 ((q+1 : ℕ) : ℝ)) := by
  have hsum : Tendsto
      (fun n => ∑ i : Fin (q+1), coefficient n (i.val+1) ^ 2)
      atTop (𝓝 (∑ _i : Fin (q+1), (1 : ℝ))) := by
    apply tendsto_finset_sum
    intro i _
    simpa only [one_pow] using (coefficient_tendsto_one (i.val+1)).pow 2
  have hden : Tendsto (fun n => coefficient n 1 ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa only [one_pow] using (coefficient_tendsto_one 1).pow 2
  convert hsum.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
  all_goals
    first | rfl | simp [squaredErrorRatio]

#print axioms coefficient_sq_strictAnti
#print axioms squaredErrorRatio_tendsto

end NLA.TR04.AllOrderSharp
