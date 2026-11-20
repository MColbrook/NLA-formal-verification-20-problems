module

public import NLA.RA02.PaperKyFan
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

def headEnergy {n : ℕ} (k : ℕ) (v : Fin n → ℂ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), Complex.normSq (v i)

def headProbe {n : ℕ} (k : ℕ) (v : Fin n → ℂ) : Fin n → ℂ :=
  fun i => if i.val < k then v i / (Real.sqrt (headEnergy k v) : ℂ) else 0

theorem headProbe_supported {n : ℕ} (k : ℕ) (v : Fin n → ℂ) :
    ∀ i, k ≤ i.val → headProbe k v i = 0 := by
  intro i hi
  simp [headProbe, Nat.not_lt.mpr hi]

theorem headProbe_norm {n : ℕ} (k : ℕ) (v : Fin n → ℂ) (hh : 0 < headEnergy k v) :
    ∑ i, Complex.normSq (headProbe k v i) = 1 := by
  have hs : Real.sqrt (headEnergy k v) ^ 2 = headEnergy k v := Real.sq_sqrt hh.le
  calc
    (∑ i, Complex.normSq (headProbe k v i)) =
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), Complex.normSq (v i)) /
          headEnergy k v := by
      simp [headProbe, apply_ite, map_div₀, Complex.normSq_ofReal, ← pow_two, hs,
        Finset.sum_filter, Finset.sum_div, ite_div]
    _ = 1 := div_self (ne_of_gt hh)

theorem headProbe_weighted_inner {n : ℕ} (k : ℕ) (a : Fin n → ℝ) (v : Fin n → ℂ) :
    (∑ i, star (headProbe k v i) * ((a i : ℂ) * v i)) =
      ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i * Complex.normSq (v i) : ℝ) : ℂ) /
        (Real.sqrt (headEnergy k v) : ℂ) := by
  rw [Finset.sum_filter, Complex.ofReal_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k
  · simp only [headProbe, hi, if_true, map_div₀, Complex.star_def, Complex.conj_ofReal,
      Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    ring
  · simp [headProbe, hi]

theorem headProbe_weighted_norm {n : ℕ} (k : ℕ) (a : Fin n → ℝ) (v : Fin n → ℂ)
    (hh : 0 < headEnergy k v) :
    (∑ i, (a i : ℂ) * star (headProbe k v i) * headProbe k v i) =
      ((∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i * Complex.normSq (v i) : ℝ) : ℂ) /
        (headEnergy k v : ℂ) := by
  have hs : (Real.sqrt (headEnergy k v) : ℂ)^2 = (headEnergy k v : ℂ) := by
    exact_mod_cast Real.sq_sqrt hh.le
  rw [Finset.sum_filter, Complex.ofReal_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k
  · simp only [headProbe, hi, if_true, map_div₀, Complex.star_def, Complex.conj_ofReal,
      Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    rw [← hs]
    ring
  · simp [headProbe, hi]

#print axioms headProbe_norm
#print axioms headProbe_weighted_inner
#print axioms headProbe_weighted_norm
end NLA.RA02.Paper
