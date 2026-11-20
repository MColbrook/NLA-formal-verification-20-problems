module

public import NLA.MF12.PaperParameters
public import NLA.MF12.GapBounds
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

theorem parameter_logarithmic_gap (lam : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (n : ℕ) (hn : lam⁻¹ ≤ (n : ℝ)) :
    ∃ q : ℕ, 1 ≤ q ∧ (lam⁻¹)^q ≤ (n : ℝ) ∧ (n : ℝ) < (lam⁻¹)^(q+1) ∧
      1 ≤ n/(q+1) ∧ (1/4:ℝ) ≤ (n/(q+1):ℕ)*parameterLoss lam q := by
  have hb4 : (4:ℝ) ≤ lam⁻¹ := by
    rw [← one_div, le_div_iff₀ hlam]
    linarith
  obtain ⟨q,hpow,hnext⟩ := exists_nat_pow_near (by linarith : 1 ≤ (n:ℝ))
    (by linarith : 1 < lam⁻¹)
  have hq : 1 ≤ q := by
    by_contra h
    have hz : q = 0 := by omega
    simp only [hz, zero_add, pow_one] at hnext
    linarith
  have hfour : (4:ℝ)^q ≤ (n:ℝ) :=
    (pow_le_pow_left₀ (by norm_num) hb4 q).trans hpow
  have hfourN : 4^q ≤ n := by exact_mod_cast hfour
  have hshort := two_mul_succ_le_four_pow q hq
  have hqn : q+1 ≤ n := by omega
  let k := n/(q+1)
  have hk : 1 ≤ k := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hqn)
  have hmod : n%(q+1) < q+1 := Nat.mod_lt _ (by omega)
  have heq : n%(q+1)+(q+1)*k = n := Nat.mod_add_div n (q+1)
  have hdiv : n < (k+1)*(q+1) := by nlinarith
  have hkd : k+1 ≤ 2*k := by omega
  have hqd : q+1 ≤ 2*q := by omega
  have hfirst := Nat.mul_le_mul_right (q+1) hkd
  have hsecond := Nat.mul_le_mul_left (2*k) hqd
  have hmassN : n ≤ 4*k*q := by nlinarith
  have hmassR : (n:ℝ) ≤ 4*(k:ℝ)*(q:ℝ) := by exact_mod_cast hmassN
  have hp : 0 < (lam⁻¹)^q := by positivity
  have hmass : (1/4:ℝ) ≤ ((k:ℝ)*(q:ℝ))/(lam⁻¹)^q := by
    apply (le_div_iff₀ hp).mpr
    linarith
  refine ⟨q,hq,hpow,hnext,hk,?_⟩
  simpa [parameterLoss, div_eq_mul_inv, inv_pow, mul_assoc, k] using hmass

theorem parameter_gain_div_loss (lam α : ℝ) (hlam : 0 < lam) (q : ℕ) (hq : 1 ≤ q) :
    parameterGain (Real.rpow lam (1-α)) q / parameterLoss lam q =
      Real.rpow ((lam⁻¹)^q) α := by
  have hqR : (q:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0 < q)
  have hp : 0 < lam^q := pow_pos hlam q
  calc
    _ = (lam^q)^(1-α)/(lam^q) := by
      unfold parameterGain parameterLoss
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_pow_comm hlam.le]
      field_simp [hqR, hp.ne']
    _ = (lam^q)^((1-α)-1) := (Real.rpow_sub_one hp.ne' (1-α)).symm
    _ = _ := by
      rw [show (1-α)-1 = -α by ring, Real.rpow_neg_eq_inv_rpow, inv_pow]
      rfl

theorem sharp_loss_decay (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (k : ℕ) (hmass : (1/4:ℝ) ≤ (k:ℝ)*ell) :
    1-Real.exp (-1/4) ≤ 1-(1-ell)^k := by
  have hb : 1-ell ≤ Real.exp (-ell) := by
    have h := Real.add_one_le_exp (-ell)
    linarith
  have hpow := pow_le_pow_left₀ (by linarith : 0 ≤ 1-ell) hb k
  have he : (Real.exp (-ell))^k = Real.exp (-(k:ℝ)*ell) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hpow
  have hfinal := hpow.trans (Real.exp_le_exp.mpr (by linarith : -(k:ℝ)*ell ≤ -1/4))
  linarith

#print axioms parameter_logarithmic_gap
#print axioms sharp_loss_decay
end NLA.MF12.Paper
