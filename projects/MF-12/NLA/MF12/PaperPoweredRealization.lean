module

public import NLA.MF12.PaperPoweredLower
public import NLA.MF12.PaperDyadic
public import NLA.MF12.RootLimit

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace NLA.MF12.Paper

theorem powered_fractional_distinct (α : ℝ) (k : ℕ) :
    (fractionalMatrix α)^k ≠ resetMatrix := by
  intro h
  have he := congrArg (fun B : Square 6 => B 0 1) h
  rw [fractionalMatrix_power] at he
  norm_num [fractionalPowerForm, resetMatrix, sourceV, sourceU,
    Matrix.mul_apply, Fin.sum_univ_two] at he

theorem powered_fractional_realization (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (k : ℕ) (hk : 1 ≤ k) :
    (fractionalMatrix α)^k ≠ resetMatrix ∧
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      (∀ n : ℕ, 1 ≤ n →
        c*Real.rpow (n : ℝ) α ≤ familyGrowth (pairFamily ((fractionalMatrix α)^k) resetMatrix) n ∧
        familyGrowth (pairFamily ((fractionalMatrix α)^k) resetMatrix) n ≤ C*Real.rpow (n : ℝ) α) ∧
      Tendsto (fun n : ℕ => Real.rpow
        (familyGrowth (pairFamily ((fractionalMatrix α)^k) resetMatrix) n) (1/(n : ℝ))) atTop (𝓝 1) := by
  let c := poweredLowerConstant k α
  let C := fractionalUpper α*Real.rpow (k : ℝ) α
  have hc : 0 < c := by
    dsimp [c, poweredLowerConstant]
    exact div_pos (Real.rpow_pos_of_pos (by positivity) _) (by norm_num)
  have hb := powered_fractional_growth α hα hα1 k hk
  have hcompare : c ≤ C := by
    have h := (hb 1 le_rfl).1.trans (hb 1 le_rfl).2
    simpa only [c, C, Nat.cast_one, Real.rpow_eq_pow, Real.one_rpow, mul_one] using h
  refine ⟨powered_fractional_distinct α k, c, C, hc, hcompare, hb, ?_⟩
  exact roots_of_polynomial_growth _ α c C hα.le hc (hc.trans_le hcompare) hb

theorem dyadic_fractional_realization (p k : ℕ) (hp : 0 < p) (hpk : p < k) :
    ∃ A P : Square 6, A ≠ P ∧ (∀ i j, IsDyadic (A i j) ∧ IsDyadic (P i j)) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        (∀ n : ℕ, 1 ≤ n →
          c*Real.rpow (n : ℝ) ((p : ℝ)/(k : ℝ)) ≤ familyGrowth (pairFamily A P) n ∧
          familyGrowth (pairFamily A P) n ≤ C*Real.rpow (n : ℝ) ((p : ℝ)/(k : ℝ))) ∧
        Tendsto (fun n : ℕ => Real.rpow (familyGrowth (pairFamily A P) n) (1/(n : ℝ))) atTop (𝓝 1) := by
  have hk : 1 ≤ k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hα : 0 < (p : ℝ)/(k : ℝ) := div_pos hpR hkR
  have hα1 : (p : ℝ)/(k : ℝ) < 1 := (div_lt_one hkR).mpr (by exact_mod_cast hpk)
  obtain ⟨hdist, hg⟩ := powered_fractional_realization ((p : ℝ)/(k : ℝ)) hα hα1 k hk
  exact ⟨(fractionalMatrix ((p : ℝ)/(k : ℝ)))^k, resetMatrix, hdist,
    fun i j => ⟨powered_fractional_entries_dyadic p k hk hpk.le i j, reset_entries_dyadic i j⟩, hg⟩

#print axioms dyadic_fractional_realization
end NLA.MF12.Paper
