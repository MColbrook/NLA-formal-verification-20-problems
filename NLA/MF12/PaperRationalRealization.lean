module

public import NLA.MF12.PaperPoweredRealization
public import NLA.MF12.PaperTensorGrowth
public import NLA.MF12.PaperRealizationDefinitions
public import Mathlib.Algebra.Order.Floor.Semifield

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Topology Classical
noncomputable section
namespace NLA.MF12.Paper

theorem integer_realization (m : ℕ) :
    Realizes (jordanMatrix m) 0 (m : ℝ) := by
  have hJ := jordan_growth_estimates m
  have hb : ∀ n : ℕ, 1 ≤ n →
      jordanLower m * Real.rpow (n : ℝ) (m : ℝ) ≤
        familyGrowth (pairFamily (jordanMatrix m) 0) n ∧
      familyGrowth (pairFamily (jordanMatrix m) 0) n ≤
        ((m+1 : ℕ) : ℝ) * Real.rpow (n : ℝ) (m : ℝ) := by
    intro n hn
    rw [integer_family_growth m n hn]
    simpa only [Real.rpow_eq_pow, Real.rpow_natCast] using hJ.2.2 n hn
  have hcC : jordanLower m ≤ ((m+1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_one, Real.rpow_eq_pow, Real.one_rpow, mul_one] using
      (hb 1 le_rfl).1.trans (hb 1 le_rfl).2
  exact ⟨hJ.2.1, jordanLower m, ((m+1 : ℕ) : ℝ), hJ.1, hcC, hb,
    roots_of_polynomial_growth _ _ _ _ (Nat.cast_nonneg m) hJ.1 (by positivity) hb⟩

theorem ratio_dyadic_realization (p k : ℕ) (hk : 1 ≤ k) :
    ∃ d : ℕ, d = paperDimension ((p : ℝ)/(k : ℝ)) ∧ 1 ≤ d ∧
      ∃ A P : Square d, Realizes A P ((p : ℝ)/(k : ℝ)) ∧
        ∀ i j, IsDyadic (A i j) ∧ IsDyadic (P i j) := by
  have hk0 : k ≠ 0 := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hf : ⌊(p : ℝ)/(k : ℝ)⌋₊ = p/k := by rw [Nat.floor_div_natCast, Nat.floor_natCast]
  have he : ((p%k : ℕ) : ℝ)/(k : ℝ) + ((p/k : ℕ) : ℝ) = (p : ℝ)/(k : ℝ) := by
    apply (eq_div_iff hkR.ne').mpr
    have hn : p%k + (p/k)*k = p := by simpa only [Nat.mul_comm] using Nat.mod_add_div p k
    have hnR : ((p%k : ℕ) : ℝ) + ((p/k : ℕ) : ℝ)*(k : ℝ) = p := by exact_mod_cast hn
    field_simp
    simpa only [mul_comm] using hnR
  by_cases hr : p%k = 0
  · have hexp : (p : ℝ)/(k : ℝ) = ((p/k : ℕ) : ℝ) := by simpa only [hr, Nat.cast_zero, zero_div, zero_add] using he.symm
    refine ⟨p/k+1, ?_, by omega, jordanMatrix (p/k), 0, ?_, ?_⟩
    · simp [paperDimension, hf, hexp]
    · rw [hexp]
      exact integer_realization (p/k)
    · intro i j
      exact ⟨jordan_entries_dyadic _ i j, by simpa using dyadic_int 0⟩
  · have hrpos : 0 < p%k := by omega
    have hrlt : p%k < k := Nat.mod_lt _ (by omega)
    have hα : 0 < ((p%k : ℕ) : ℝ)/(k : ℝ) := div_pos (by exact_mod_cast hrpos) hkR
    have hnot : (p : ℝ)/(k : ℝ) ≠ ((p/k : ℕ) : ℝ) := by linarith
    obtain ⟨A, P, hAP, hdy, c, C, hc, hcC, hb, _⟩ :=
      dyadic_fractional_realization (p%k) k hrpos hrlt
    have ht := tensor_pair_growth (by norm_num : 1 ≤ 6) A P hAP
      (((p%k : ℕ) : ℝ)/(k : ℝ)) hα.le c C hc hcC hb (p/k)
    refine ⟨6*(p/k+1), ?_, by omega, tensor A (jordanMatrix (p/k)),
      tensor P (jordanMatrix (p/k)), ?_, ?_⟩
    · simp [paperDimension, hf, hnot]
    · simpa only [Realizes, he] using ht
    · intro i j
      exact ⟨tensor_entries_dyadic A _ (fun i j => (hdy i j).1) (jordan_entries_dyadic _) i j,
        tensor_entries_dyadic P _ (fun i j => (hdy i j).2) (jordan_entries_dyadic _) i j⟩

theorem rational_dyadic_realization (q : ℚ) (hq : 0 ≤ q) :
    ∃ d : ℕ, d = paperDimension (q : ℝ) ∧ 1 ≤ d ∧
      ∃ A P : Square d, Realizes A P (q : ℝ) ∧
        ∀ i j, IsDyadic (A i j) ∧ IsDyadic (P i j) := by
  have he : (q : ℝ) = (q.num.toNat : ℝ)/(q.den : ℝ) := by
    rw [Rat.cast_def, ← Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)]
    simp only [Int.cast_natCast, Int.toNat_natCast]
  rw [he]
  exact ratio_dyadic_realization _ _ (by have := q.den_pos; omega)

#print axioms rational_dyadic_realization
end NLA.MF12.Paper
