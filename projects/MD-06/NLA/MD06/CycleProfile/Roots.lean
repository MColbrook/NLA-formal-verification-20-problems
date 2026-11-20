module

public import NLA.MD06.CycleProfile.ScalarBounds
public import NLA.MD06.CycleProfile.RootDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CycleProfile
open Set

theorem actual_balance_root_unique {R : ℕ} (hR : 4 ≤ R) :
    ∃! t : ℝ, t ∈ Icc 0 1 ∧ Balance R t = 2 * Real.pi := by
  have hmem : 2 * Real.pi ∈ Icc (Balance R 0) (Balance R 1) := by
    rw [actual_balance_zero]
    exact ⟨by positivity, (actual_balance_one_gt hR).le⟩
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (actual_balance_continuous R).continuousOn hmem
  refine ⟨t, ⟨ht, he⟩, ?_⟩
  intro y hy
  exact (actual_balance_strictMono R).injOn hy.1 ht (hy.2.trans he.symm)


theorem actual_root_spec {R : ℕ} (hR : 4 ≤ R) :
    Root R ∈ Icc 0 1 ∧ Balance R (Root R) = 2 * Real.pi := by
  exact Classical.epsilon_spec (actual_balance_root_unique hR).exists

theorem actual_root_interval {R : ℕ} (hR : 4 ≤ R) : Root R ∈ Ioo (1/2) 1 := by
  have hr := actual_root_spec hR
  have hl : (1/2 : ℝ) < Root R := by
    by_contra hh
    have hm := (actual_balance_strictMono R).monotoneOn
      hr.1 (by norm_num : (1/2 : ℝ) ∈ Icc 0 1) (le_of_not_gt hh)
    linarith [actual_balance_half_lt R, hr.2]
  have hu : Root R < 1 := by
    by_contra hh
    have he : Root R = 1 := le_antisymm hr.1.2 (le_of_not_gt hh)
    rw [he] at hr
    linarith [actual_balance_one_gt hR, hr.2]
  exact ⟨hl, hu⟩

theorem actual_root_radius_antitone {R S : ℕ} (hR : 4 ≤ R) (hRS : R ≤ S) : Root S ≤ Root R := by
  have hr := actual_root_spec hR
  have hs := actual_root_spec (hR.trans hRS)
  by_contra hh
  have hlt := (actual_balance_strictMono R) hr.1 hs.1 (lt_of_not_ge hh)
  have hm := actual_balance_radius_monotone hRS hs.1.1
  linarith [hr.2, hs.2]

theorem actual_root_cosine_positive {R : ℕ} (hR : 4 ≤ R) :
    0 < Real.sqrt (1 - (Root R)^2) := by
  apply Real.sqrt_pos.mpr
  have hr := actual_root_interval hR
  nlinarith [hr.1, hr.2]

theorem actual_root_uniform_cosine {R : ℕ} (hR : 4 ≤ R) :
    Real.sqrt (1 - (Root 4)^2) ≤ Real.sqrt (1 - (Root R)^2) := by
  apply Real.sqrt_le_sqrt
  have h := actual_root_radius_antitone (by omega : 4 ≤ 4) hR
  have h4 := actual_root_interval (by omega : 4 ≤ 4)
  have hr := actual_root_interval hR
  nlinarith [h4.1, h4.2, hr.1, hr.2]
end Reference.MD06CycleProfile
