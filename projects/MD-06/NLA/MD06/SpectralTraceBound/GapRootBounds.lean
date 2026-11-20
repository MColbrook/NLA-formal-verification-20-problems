module

public import NLA.MD06.SpectralTraceBound.ScalarRoots

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06SpectralTrace

theorem actual_gap_root_rational_bounds : 7 / 4 ≤ GapRoot ∧ GapRoot ≤ 9 / 5 := by
  have hs : Real.sqrt ((41 : ℝ) / 100) ^ 2 = 41 / 100 :=
    Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg ((41 : ℝ) / 100)
  dsimp [GapRoot]
  constructor <;> nlinarith

theorem actual_gap_root_fourth_power_exceeds_eight : (8 : ℝ) < GapRoot ^ 4 := by
  have hb := actual_gap_root_rational_bounds.1
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 7 / 4) hb 4
  norm_num at hp
  linarith

theorem actual_gap_root_geometric_ratio_bounds :
    0 < 8 / GapRoot ^ 4 ∧ 8 / GapRoot ^ 4 < 1 := by
  have hp := actual_gap_root_fourth_power_exceeds_eight
  constructor
  · positivity
  · exact (div_lt_one (by linarith)).2 hp

#print axioms actual_gap_root_rational_bounds
#print axioms actual_gap_root_fourth_power_exceeds_eight
#print axioms actual_gap_root_geometric_ratio_bounds

end Reference.RootMD06SpectralTrace
