module

public import NLA.MF12.PaperSharpGaps
public import NLA.MF12.PaperSharpRayleigh

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

theorem parameter_family_sharp_lower (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) (n : ℕ) (hn : 1 ≤ n) :
    ((1-Real.exp (-1/4))/Real.sqrt 2*Real.rpow lam α)*Real.rpow (n:ℝ) α ≤
      familyGrowth (pairFamily (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix) n := by
  let μ := Real.rpow lam (1-α)
  let δ := 1-Real.exp (-1/4)
  have hδ : 0 ≤ δ := by
    have h := Real.exp_le_one_iff.mpr (by norm_num : (-1/4:ℝ) ≤ 0)
    dsimp [δ]
    linarith
  have hδ1 : δ ≤ 1 := by dsimp [δ]; have := Real.exp_pos (-1/4); linarith
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by
    have h := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
    nlinarith
  have hG : 1 ≤ familyGrowth (pairFamily (parameterMatrix lam μ) resetMatrix) n := by
    apply (parameter_power_norm_ge_one lam μ n).trans
    simpa only [binaryProduct_replicate_false, List.length_replicate] using
      binaryProduct_le_familyGrowth (parameterMatrix lam μ) resetMatrix (List.replicate n false)
  change (δ/Real.sqrt 2*Real.rpow lam α)*Real.rpow (n:ℝ) α ≤ _
  by_cases hsmall : (n:ℝ) < lam⁻¹
  · have hl : lam*(n:ℝ) ≤ 1 := by
      have hh : (n:ℝ) < 1/lam := by simpa only [one_div] using hsmall
      have := (lt_div_iff₀ hlam).mp hh
      nlinarith
    have hprod : Real.rpow lam α*Real.rpow (n:ℝ) α ≤ 1 := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.mul_rpow hlam.le (Nat.cast_nonneg n)]
      exact Real.rpow_le_one (by positivity) hl hα.le
    have hc : δ/Real.sqrt 2 ≤ 1 := (div_le_one hs).mpr (hδ1.trans hs1)
    have hc0 : 0 ≤ δ/Real.sqrt 2 := div_nonneg hδ hs.le
    calc
      _ = (δ/Real.sqrt 2)*(Real.rpow lam α*Real.rpow (n:ℝ) α) := by ring
      _ ≤ δ/Real.sqrt 2 := by simpa using mul_le_mul_of_nonneg_left hprod hc0
      _ ≤ 1 := hc
      _ ≤ _ := hG
  · have hnlam : lam⁻¹ ≤ (n:ℝ) := le_of_not_gt hsmall
    obtain ⟨q,hq,hpow,hnext,hk,hmass⟩ := parameter_logarithmic_gap lam hlam hlamq n hnlam
    let k := n/(q+1)
    let r := n-k*(q+1)
    have hell := parameter_loss_bounds lam hlam hlamq q hq
    have hdecay : δ ≤ 1-(1-parameterLoss lam q)^k :=
      sharp_loss_decay _ hell.1.le (by linarith [hell.2]) k hmass
    have hratio0 : 0 ≤ parameterGain μ q/parameterLoss lam q := by
      rw [parameter_gain_div_loss lam α hlam q hq]
      exact Real.rpow_nonneg (pow_nonneg (inv_nonneg.mpr hlam.le) q) α
    have hscale : Real.rpow lam α*Real.rpow (n:ℝ) α ≤
        parameterGain μ q/parameterLoss lam q := by
      rw [parameter_gain_div_loss lam α hlam q hq]
      simp only [Real.rpow_eq_pow]
      rw [← Real.mul_rpow hlam.le (Nat.cast_nonneg n)]
      apply Real.rpow_le_rpow (by positivity) _ hα.le
      have hnext' : (n:ℝ) < (lam⁻¹)^q/lam := by
        simpa [pow_succ, div_eq_mul_inv] using hnext
      have := (lt_div_iff₀ hlam).mp hnext'
      nlinarith
    obtain ⟨w,hw,hprod⟩ := parameter_repeat_word lam μ q n
    have hentry := parameter_repeat_rayleigh lam μ q k r hell.1.ne'
    have hmul := mul_le_mul_of_nonneg_left hdecay hratio0
    have hsc := mul_le_mul_of_nonneg_left hscale hδ
    have hbound : δ*(Real.rpow lam α*Real.rpow (n:ℝ) α) ≤
        Real.sqrt 2*spectralNorm (binaryProduct (parameterMatrix lam μ) resetMatrix w) := by
      rw [hprod]
      change _ ≤ Real.sqrt 2*spectralNorm (parameterMatrix lam μ^r*(resetMatrix*parameterMatrix lam μ^q)^k)
      nlinarith
    have hnorm : (δ/Real.sqrt 2*Real.rpow lam α)*Real.rpow (n:ℝ) α ≤
        spectralNorm (binaryProduct (parameterMatrix lam μ) resetMatrix w) := by
      calc
        _ = (δ*(Real.rpow lam α*Real.rpow (n:ℝ) α))/Real.sqrt 2 := by ring
        _ ≤ _ := (div_le_iff₀ hs).mpr (by simpa [mul_comm] using hbound)
    exact hnorm.trans (by simpa [hw, μ, Real.rpow_eq_pow] using binaryProduct_le_familyGrowth (parameterMatrix lam μ) resetMatrix w)

#print axioms parameter_family_sharp_lower
end NLA.MF12.Paper
