module

public import NLA.MF05.PaperCyclicObstruction
public import NLA.MF05.PaperCyclicCharacteristic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF05.Paper.Cyclic

theorem perturbation_radius_delta (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    realRadius {perturbation n δ} = δ ^ (1 / ((n+1 : ℕ) : ℝ)) := by
  have hr : 0 < δ ^ (1 / ((n+1 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hδ _
  have hp : (δ ^ (1 / ((n+1 : ℕ) : ℝ)))^(n+1) = δ := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hδ.le (by omega : n+1 ≠ 0)
  simpa only [hp] using perturbation_radius n _ hr

theorem shift_norm_le_one (n : ℕ) : realSpectralNorm (shift n) ≤ 1 := by
  simpa only [perturbation_zero] using perturbation_norm_le_one n 0 (by norm_num)

#print axioms perturbation_radius_delta
end NLA.MF05.Paper.Cyclic
