module

public import NLA.RA09.Paper.SharpFamily
public import NLA.RA09.Paper.SharpnessLimits
public import NLA.RA09.PaperSharpnessDefinitions

@[expose] public section

/-! Sharpness along the paper's actual matrix family with N = L, b = exp(-L)
and p = L^(-2). Both conventions use the same selected eigenvectors. -/
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace NLA.RA09.Paper

def sharpPower (N : ℕ) : ℝ := 1 / (N : ℝ)^2
def sharpSmall (N : ℕ) : ℝ := Real.exp (-(N : ℝ))
def sharpFunction (N : ℕ) (x : ℝ) : ℝ := x ^ sharpPower N
def sharpDataB (N : ℕ) : OrderedSpectralData (sharpB N (sharpSmall N)) :=
  Classical.choice (orderedSpectral_exists_proved _
    (sharpB_psd N _ (Real.exp_pos _).le))

theorem sharpPower_range (N : ℕ) (hN : 2 ≤ N) : 0 < sharpPower N ∧ sharpPower N < 1 := by
  have h : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold sharpPower
  constructor
  · positivity
  · apply (div_lt_one (by positivity)).2
    nlinarith

theorem sharpSmall_range (N : ℕ) (hN : 0 < N) : 0 < sharpSmall N ∧ sharpSmall N < 1 := by
  refine ⟨Real.exp_pos _, ?_⟩
  apply Real.exp_lt_one_iff.mpr
  have : (0 : ℝ) < N := by exact_mod_cast hN
  linarith

theorem sharpFunction_small (N : ℕ) (hN : 0 < N) :
    sharpFunction N (sharpSmall N) = Real.exp (-(1/(N : ℝ))) := by
  unfold sharpFunction sharpSmall sharpPower
  rw [← Real.exp_mul]
  congr 1
  have : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
  field_simp

theorem sharpFunction_admissible (N : ℕ) (hN : 2 ≤ N) :
    PaperAdmissibleFunction (sharpFunction N) :=
  power_admissible (sharpPower_range N hN).1 (sharpPower_range N hN).2.le

def actualSquaredRatio (N : ℕ) : ℝ :=
  (frobeniusSquared (functionalCalculus (sharpFunction N) (sharpA N) -
      functionTruncation (sharpDataB N) (sharpFunction N) 1) -
    functionTail (sharpDataA N) (sharpFunction N) 1) /
  (frobeniusSquared (sharpA N - sharpB N (sharpSmall N)) - spectralTail (sharpDataA N) 1)

def actualNormRatio (N : ℕ) : ℝ :=
  (frobeniusNorm (functionalCalculus (sharpFunction N) (sharpA N) -
      functionTruncation (sharpDataB N) (sharpFunction N) 1) /
      Real.sqrt (functionTail (sharpDataA N) (sharpFunction N) 1) - 1) /
  (frobeniusNorm (sharpA N - sharpB N (sharpSmall N)) /
      Real.sqrt (spectralTail (sharpDataA N) 1) - 1)

theorem actualSquaredRatio_eq (N : ℕ) (hN : 2 ≤ N) :
    actualSquaredRatio N = squaredExcessRatio (N : ℝ) := by
  have hp := sharpPower_range N hN
  have hf : Continuous (sharpFunction N) := Real.continuous_rpow_const hp.1.le
  have hf0 : sharpFunction N 0 = 0 := Real.zero_rpow (ne_of_gt hp.1)
  have hf1 : sharpFunction N 1 = 1 := Real.one_rpow _
  unfold actualSquaredRatio
  rw [sharp_output_error _ _ _ hf hf0 hf1, sharpA_function_tail _ _ hf0 hf1,
    sharp_input_error, sharpA_tail, sharpFunction_small N (by omega)]
  unfold squaredExcessRatio inputExcess outputExcess sharpSmall
  congr 1 <;> ring

theorem actualNormRatio_eq (N : ℕ) (hN : 2 ≤ N) :
    actualNormRatio N = normExcessRatio (N : ℝ) := by
  have hp := sharpPower_range N hN
  have hf : Continuous (sharpFunction N) := Real.continuous_rpow_const hp.1.le
  have hf0 : sharpFunction N 0 = 0 := Real.zero_rpow (ne_of_gt hp.1)
  have hf1 : sharpFunction N 1 = 1 := Real.one_rpow _
  unfold actualNormRatio
  rw [sharp_norm_output N (by omega) _ _ hf hf0 hf1, sharp_norm_input N (by omega),
    sharpFunction_small N (by omega)]
  rfl

theorem actualSquaredRatio_limit : Tendsto actualSquaredRatio atTop (𝓝 2) := by
  have h := squaredExcessRatio_limit.comp tendsto_natCast_atTop_atTop
  apply Tendsto.congr' (f₁ := fun N : ℕ => squaredExcessRatio (N : ℝ)) ?_ h
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (actualSquaredRatio_eq N hN).symm

theorem actualNormRatio_limit : Tendsto actualNormRatio atTop (𝓝 2) := by
  have h := normExcessRatio_limit.comp tendsto_natCast_atTop_atTop
  apply Tendsto.congr' (f₁ := fun N : ℕ => normExcessRatio (N : ℝ)) ?_ h
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (actualNormRatio_eq N hN).symm

theorem simultaneous_sharpness (γ : ℝ) (hγ : γ < 2) :
    ∃ N : ℕ, 2 ≤ N ∧ γ < actualSquaredRatio N ∧ γ < actualNormRatio N := by
  have hs := actualSquaredRatio_limit.eventually (eventually_gt_nhds hγ)
  have hn := actualNormRatio_limit.eventually (eventually_gt_nhds hγ)
  obtain ⟨N, hN, hSN, hNN⟩ := ((eventually_ge_atTop 2).and (hs.and hn)).exists
  exact ⟨N, hN, hSN, hNN⟩

theorem unordered_sharpness (γ : ℝ) (hγ : γ < 2) : UnorderedSharpnessWitness γ := by
  obtain ⟨N, hN, hs, hn⟩ := simultaneous_sharpness γ hγ
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := sharpPower_range N hN
  have hsq : 0 < frobeniusSquared (sharpA N - sharpB N (sharpSmall N)) -
      spectralTail (sharpDataA N) 1 := by
    rw [sharp_input_error, sharpA_tail]
    nlinarith [sq_nonneg (sharpSmall N)]
  have hnorm : 0 < frobeniusNorm (sharpA N - sharpB N (sharpSmall N)) /
      Real.sqrt (spectralTail (sharpDataA N) 1) - 1 := by
    rw [sharp_norm_input N (by omega)]
    have hd : 0 < (1+sharpSmall N^2)/(N : ℝ) := div_pos (by positivity) hNr
    have hlt : 1 < Real.sqrt (1+(1+sharpSmall N^2)/(N : ℝ)) := by
      rw [Real.lt_sqrt (by norm_num)]
      nlinarith
    linarith
  refine ⟨N+2, by omega, sharpPower N, sharpA N, sharpB N (sharpSmall N),
    sharpDataA N, sharpDataB N, hp.1, hp.2, sharpB_rank N _,
    sharpA_cutoff N (by omega), ?_, hsq, hnorm, ?_, ?_⟩
  · rw [sharpA_tail]
    exact hNr
  · exact (lt_div_iff₀ hsq).mp hs
  · exact (lt_div_iff₀ hnorm).mp hn

#print axioms actualSquaredRatio_limit
#print axioms actualNormRatio_limit
#print axioms simultaneous_sharpness
#print axioms unordered_sharpness

end NLA.RA09.Paper
