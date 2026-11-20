module

public import NLA.MF12.PaperPoweredGaps

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

def poweredLowerWord (k n : ℕ) : List Bool :=
  if n < 4^k then List.replicate n false else
    (List.replicate (poweredCount k n)
      (List.replicate (poweredGap k n) false ++ [true])).flatten ++
      List.replicate (poweredRemainder k n) false

def poweredLowerConstant (k : ℕ) (α : ℝ) : ℝ :=
  Real.rpow (((4 : ℝ)^k)⁻¹) α/10

theorem powered_lower_word_exact (α : ℝ) (k n : ℕ) :
    (poweredLowerWord k n).length = n ∧
    binaryProduct ((fractionalMatrix α)^k) resetMatrix (poweredLowerWord k n) =
      if n < 4^k then (fractionalMatrix α)^(k*n) else
        (fractionalMatrix α)^(k*poweredRemainder k n) *
          (resetMatrix*(fractionalMatrix α)^(k*poweredGap k n))^(poweredCount k n) := by
  have hr : poweredRemainder k n+poweredCount k n*(poweredGap k n+1) = n :=
    Nat.sub_add_cancel (Nat.div_mul_le_self n (poweredGap k n+1))
  by_cases hn : n < 4^k
  · simp [poweredLowerWord, hn, pow_mul]
  · simp only [poweredLowerWord, if_neg hn]
    constructor
    · simpa only [List.length_append, List.length_flatten, List.map_replicate,
        List.sum_replicate, List.length_replicate, List.length_singleton,
        nsmul_eq_mul, Nat.cast_id, add_comm] using hr
    · rw [binaryProduct_append, binaryProduct_replicate_false,
        binaryProduct_flatten_replicate, binaryProduct_append, binaryProduct_replicate_false]
      simp [binaryProduct_cons, pow_mul]

theorem powered_gain_ratio_lower (α : ℝ) (hα : 0 < α) (k : ℕ) (hk : 1 ≤ k)
    (n : ℕ) (hn : 4^k ≤ n) :
    Real.rpow (((4 : ℝ)^k)⁻¹) α * Real.rpow (n : ℝ) α ≤
      gain α (k*poweredGap k n)/loss (k*poweredGap k n) := by
  have hg := powered_logarithmic_gap_bounds k hk n hn
  have hkg : 1 ≤ k*poweredGap k n := one_le_mul_of_one_le_of_one_le hk hg.1
  have hnext : (n : ℝ) < (4 : ℝ)^(k*(poweredGap k n+1)) := by exact_mod_cast hg.2.2.2.1
  have he : k*(poweredGap k n+1) = k*poweredGap k n+k := by ring
  rw [he, pow_add] at hnext
  have hp : 0 < (4 : ℝ)^k := by positivity
  have hs : ((4 : ℝ)^k)⁻¹*(n : ℝ) ≤ (4 : ℝ)^(k*poweredGap k n) := by
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ hp).mpr hnext.le
  simp only [Real.rpow_eq_pow]
  rw [gain_div_loss α _ hkg, ← Real.mul_rpow (inv_nonneg.mpr hp.le) (Nat.cast_nonneg n)]
  exact Real.rpow_le_rpow (by positivity) hs hα.le

theorem powered_lower_all_lengths (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    poweredLowerConstant k α * Real.rpow (n : ℝ) α ≤
      spectralNorm (binaryProduct ((fractionalMatrix α)^k) resetMatrix (poweredLowerWord k n)) := by
  rw [(powered_lower_word_exact α k n).2]
  by_cases hsmall : n < 4^k
  · rw [if_pos hsmall]
    have hp : 0 < (4 : ℝ)^k := by positivity
    have hnR : (n : ℝ) ≤ (4 : ℝ)^k := by exact_mod_cast hsmall.le
    have hs : ((4 : ℝ)^k)⁻¹*(n : ℝ) ≤ 1 := by
      rw [inv_mul_eq_div]
      exact (div_le_one hp).mpr hnR
    have hpow := Real.rpow_le_rpow (by positivity) hs hα.le
    rw [Real.mul_rpow (inv_nonneg.mpr hp.le) (Nat.cast_nonneg n), Real.one_rpow] at hpow
    have hnorm := fractional_power_norm_ge_one α (k*n)
    unfold poweredLowerConstant
    simp only [Real.rpow_eq_pow] at *
    nlinarith
  · rw [if_neg hsmall]
    have hnB : 4^k ≤ n := by omega
    have hg := powered_logarithmic_gap_bounds k hk n hnB
    let q := k*poweredGap k n
    let c := poweredCount k n
    let r := k*poweredRemainder k n
    have hq : 1 ≤ q := one_le_mul_of_one_le_of_one_le hk hg.1
    have hell : 0 < loss q := loss_pos q hq
    have hmass : (1/4 : ℝ) ≤ (c : ℝ)*loss q := hg.2.2.2.2.2
    have hdecay : (1/5 : ℝ) ≤ 1-(1-loss q)^c :=
      (bernoulli_loss (loss q) hell.le (loss_lt_one q) c).2 hmass
    have hratio0 : 0 ≤ gain α q/loss q := by
      rw [gain_div_loss α q hq]
      positivity
    have hentry := mul_sourceV_entry_le_norm
      ((fractionalMatrix α)^r*(resetMatrix*(fractionalMatrix α)^q)^c)
    rw [padded_repeat_compressed_entry, compressed_powers,
      triangular_geometric_power (loss q) (gain α q) hell.ne'] at hentry
    change gain α q/loss q*(1-(1-loss q)^c) ≤
      2*spectralNorm ((fractionalMatrix α)^r*(resetMatrix*(fractionalMatrix α)^q)^c) at hentry
    have hprod := mul_le_mul_of_nonneg_left hdecay hratio0
    have hscale : Real.rpow (((4 : ℝ)^k)⁻¹) α * Real.rpow (n : ℝ) α ≤ gain α q/loss q :=
      powered_gain_ratio_lower α hα k hk n hnB
    change Real.rpow (((4 : ℝ)^k)⁻¹) α/10 * Real.rpow (n : ℝ) α ≤
      spectralNorm ((fractionalMatrix α)^r*(resetMatrix*(fractionalMatrix α)^q)^c)
    nlinarith

theorem powered_fractional_growth (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 1 ≤ n) :
    poweredLowerConstant k α * Real.rpow (n : ℝ) α ≤
      familyGrowth (pairFamily ((fractionalMatrix α)^k) resetMatrix) n ∧
    familyGrowth (pairFamily ((fractionalMatrix α)^k) resetMatrix) n ≤
      (fractionalUpper α*Real.rpow (k : ℝ) α)*Real.rpow (n : ℝ) α := by
  constructor
  · have h := binaryProduct_le_familyGrowth ((fractionalMatrix α)^k) resetMatrix (poweredLowerWord k n)
    rw [(powered_lower_word_exact α k n).1] at h
    exact (powered_lower_all_lengths α hα hα1 k hk n hn).trans h
  · apply familyGrowth_le_of_binary
    intro w hw
    simpa only [hw] using powered_all_word_upper α hα hα1 k hk w (by omega)

#print axioms powered_lower_all_lengths
#print axioms powered_fractional_growth
end NLA.MF12.Paper
