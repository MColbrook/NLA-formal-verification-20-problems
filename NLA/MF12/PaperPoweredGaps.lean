module

public import NLA.MF12.PaperPoweredWords

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

def poweredGap (k n : ℕ) : ℕ := Nat.log (4^k) n
def poweredCount (k n : ℕ) : ℕ := n/(poweredGap k n+1)
def poweredRemainder (k n : ℕ) : ℕ := n-poweredCount k n*(poweredGap k n+1)

theorem powered_logarithmic_gap_bounds (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : 4^k ≤ n) :
    1 ≤ poweredGap k n ∧ 1 ≤ poweredCount k n ∧
    4^(k*poweredGap k n) ≤ n ∧ n < 4^(k*(poweredGap k n+1)) ∧
    poweredRemainder k n+poweredCount k n*(poweredGap k n+1) = n ∧
    (1/4 : ℝ) ≤ (poweredCount k n : ℝ)*loss (k*poweredGap k n) := by
  let g := poweredGap k n
  let c := poweredCount k n
  have hb : 4 ≤ 4^k := le_self_pow₀ (by norm_num : 1 ≤ (4 : ℕ)) (by omega)
  have hbase : 1 < 4^k := by omega
  have hg : 1 ≤ g := Nat.log_pos hbase hn
  have hpow : 4^(k*g) ≤ n := by
    simpa only [g, poweredGap, pow_mul] using Nat.pow_log_le_self (4^k) (by omega : n ≠ 0)
  have hnext : n < 4^(k*(g+1)) := by
    simpa only [g, poweredGap, pow_mul] using Nat.lt_pow_succ_log_self hbase n
  have hkg : g ≤ k*g := by nlinarith
  have hshort : 2*(g+1) ≤ 4^(k*g) :=
    (two_mul_succ_le_four_pow g hg).trans (pow_le_pow_right₀ (by norm_num) hkg)
  have hgn : g+1 ≤ n := by omega
  have hc : 1 ≤ c := by
    change 1 ≤ n/(g+1)
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hgn)
  have hmod : n%(g+1) < g+1 := Nat.mod_lt _ (by omega)
  have heq : n%(g+1)+(g+1)*c = n := Nat.mod_add_div n (g+1)
  have hdiv : n < (c+1)*(g+1) := by nlinarith
  have hc2 : c+1 ≤ 2*c := by omega
  have hg2 : g+1 ≤ 2*g := by omega
  have hfirst := Nat.mul_le_mul_right (g+1) hc2
  have hsecond := Nat.mul_le_mul_left (2*c) hg2
  have hm : 4^(k*g) ≤ 4*c*(k*g) := by nlinarith
  have hmR : (4 : ℝ)^(k*g) ≤ 4*(c : ℝ)*(k*g : ℕ) := by exact_mod_cast hm
  have hpR : 0 < (4 : ℝ)^(k*g) := by positivity
  refine ⟨hg, hc, hpow, hnext, Nat.sub_add_cancel (Nat.div_mul_le_self n (g+1)), ?_⟩
  calc
    (1/4 : ℝ) ≤ ((c : ℝ)*((k*g : ℕ) : ℝ))/(4 : ℝ)^(k*g) := by
      apply (le_div_iff₀ hpR).mpr
      nlinarith
    _ = _ := by
      change ((c : ℝ)*((k*g : ℕ) : ℝ))/(4 : ℝ)^(k*g) =
        (c : ℝ)*(((k*g : ℕ) : ℝ)*baseLambda^(k*g))
      rw [baseLambda, div_pow, one_pow]
      ring

#print axioms powered_logarithmic_gap_bounds
end NLA.MF12.Paper
