module

public import NLA.MF12.Lifted
public import NLA.MF12.RootLimit
public import NLA.MF12.PaperDyadic

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Topology Classical
noncomputable section
namespace NLA.MF12.Paper

theorem tensor_pair_growth {d : ℕ} (hd : 1 ≤ d) (A P : Square d)
    (hAP : A ≠ P) (α : ℝ) (hα : 0 ≤ α) (c C : ℝ)
    (hc : 0 < c) (hcC : c ≤ C)
    (hb : ∀ n : ℕ, 1 ≤ n →
      c * Real.rpow (n : ℝ) α ≤ familyGrowth (pairFamily A P) n ∧
      familyGrowth (pairFamily A P) n ≤ C * Real.rpow (n : ℝ) α) (m : ℕ) :
    tensor A (jordanMatrix m) ≠ tensor P (jordanMatrix m) ∧
    ∃ c' C' : ℝ, 0 < c' ∧ c' ≤ C' ∧
      (∀ n : ℕ, 1 ≤ n →
        c' * Real.rpow (n : ℝ) (α + (m : ℝ)) ≤
          familyGrowth (pairFamily (tensor A (jordanMatrix m)) (tensor P (jordanMatrix m))) n ∧
        familyGrowth (pairFamily (tensor A (jordanMatrix m)) (tensor P (jordanMatrix m))) n ≤
          C' * Real.rpow (n : ℝ) (α + (m : ℝ))) ∧
      Tendsto (fun n : ℕ => Real.rpow
        (familyGrowth (pairFamily (tensor A (jordanMatrix m)) (tensor P (jordanMatrix m))) n)
        (1 / (n : ℝ))) atTop (𝓝 1) := by
  let D : ℝ := (d : ℝ) * ((m + 1 : ℕ) : ℝ)
  let c' := c * jordanLower m / D
  let C' := D * C * ((m + 1 : ℕ) : ℝ)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hD : 0 < D := mul_pos hdR (by positivity)
  have hc' : 0 < c' := div_pos (mul_pos hc (jordanLower_pos m)) hD
  have hC : 0 < C := hc.trans_le hcC
  have hg : ∀ n : ℕ, 1 ≤ n →
      c' * Real.rpow (n : ℝ) (α + (m : ℝ)) ≤
        familyGrowth (pairFamily (tensor A (jordanMatrix m)) (tensor P (jordanMatrix m))) n ∧
      familyGrowth (pairFamily (tensor A (jordanMatrix m)) (tensor P (jordanMatrix m))) n ≤
        C' * Real.rpow (n : ℝ) (α + (m : ℝ)) := by
    intro n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hJ := (jordan_growth_estimates m).2.2 n hn
    constructor
    · have hmax := (wordNorms_nonempty (pairFamily A P) (by simp [pairFamily]) n).csSup_mem
        (wordNorms_finite (pairFamily A P) n)
      rw [pair_word_norms] at hmax
      obtain ⟨w, hw, he⟩ := hmax
      have he' : familyGrowth (pairFamily A P) n = spectralNorm (binaryProduct A P w) := by
        unfold familyGrowth
        rw [pair_word_norms]
        exact he
      have hl : c * Real.rpow (n : ℝ) α ≤ spectralNorm (binaryProduct A P w) := by
        simpa only [he'] using (hb n hn).1
      have hp := mul_le_mul hl hJ.1
        (mul_nonneg (jordanLower_pos m).le (pow_nonneg hnR.le m))
        (spectralNorm_nonneg (binaryProduct A P w))
      have ht := tensor_norm_comparison d (m+1) hd (by omega)
        (binaryProduct A P w) (jordanMatrix m ^ n)
      calc
        c' * Real.rpow (n : ℝ) (α + (m : ℝ)) =
            (c * Real.rpow (n : ℝ) α * (jordanLower m * (n : ℝ)^m)) / D := by
          simp only [c', Real.rpow_eq_pow]
          rw [Real.rpow_add hnR, Real.rpow_natCast]
          ring
        _ ≤ (spectralNorm (binaryProduct A P w) * spectralNorm (jordanMatrix m ^ n)) / D :=
          div_le_div_of_nonneg_right hp hD.le
        _ ≤ spectralNorm (tensor (binaryProduct A P w) (jordanMatrix m ^ n)) := ht.2.1
        _ = spectralNorm (binaryProduct (tensor A (jordanMatrix m))
            (tensor P (jordanMatrix m)) w) := by rw [tensor_word_identity, hw]
        _ ≤ familyGrowth (pairFamily (tensor A (jordanMatrix m))
            (tensor P (jordanMatrix m))) n := by
          simpa only [hw] using binaryProduct_le_familyGrowth
            (tensor A (jordanMatrix m)) (tensor P (jordanMatrix m)) w
    · apply familyGrowth_le_of_binary
      intro w hw
      have hf := (binaryProduct_le_familyGrowth A P w).trans (by
        simpa only [hw] using (hb n hn).2)
      have hp := mul_le_mul hf hJ.2 (spectralNorm_nonneg (jordanMatrix m ^ n))
        (mul_nonneg hC.le (Real.rpow_nonneg hnR.le _))
      have ht := tensor_norm_comparison d (m+1) hd (by omega)
        (binaryProduct A P w) (jordanMatrix m ^ n)
      calc
        spectralNorm (binaryProduct (tensor A (jordanMatrix m))
            (tensor P (jordanMatrix m)) w) =
            spectralNorm (tensor (binaryProduct A P w) (jordanMatrix m ^ n)) := by
          rw [tensor_word_identity, hw]
        _ ≤ D * (spectralNorm (binaryProduct A P w) * spectralNorm (jordanMatrix m ^ n)) :=
          ht.2.2.trans_eq (by dsimp [D]; ring)
        _ ≤ D * (C * Real.rpow (n : ℝ) α * (((m+1 : ℕ) : ℝ) * (n : ℝ)^m)) :=
          mul_le_mul_of_nonneg_left hp hD.le
        _ = C' * Real.rpow (n : ℝ) (α + (m : ℝ)) := by
          simp only [C', Real.rpow_eq_pow]
          rw [Real.rpow_add hnR, Real.rpow_natCast]
          ring
  have hcompare : c' ≤ C' := by
    simpa only [Nat.cast_one, Real.rpow_eq_pow, Real.one_rpow, mul_one] using
      (hg 1 le_rfl).1.trans (hg 1 le_rfl).2
  have hJ : jordanMatrix m (0 : Fin (m+1)) 0 = 1 := by
    simpa only [pow_one] using jordan_power_diagonal m 1 0
  refine ⟨fun he => hAP (tensor_left_injective_of_entry_one _ 0 0 hJ he),
    c', C', hc', hcompare, hg, ?_⟩
  exact roots_of_polynomial_growth _ _ _ _ (add_nonneg hα (Nat.cast_nonneg m))
    hc' (hc'.trans_le hcompare) hg

theorem jordan_entries_dyadic (m : ℕ) (i j : Fin (m+1)) :
    IsDyadic (jordanMatrix m i j) := by
  have hz : IsDyadic (0 : ℝ) := by simpa using dyadic_int 0
  have ho : IsDyadic (1 : ℝ) := by simpa using dyadic_int 1
  change IsDyadic ((if i = j then (1 : ℝ) else 0) + (if i.val+1 = j.val then 1 else 0))
  apply dyadic_add
  · by_cases h : i = j <;> simp [Matrix.one_apply, h, hz, ho]
  · split_ifs <;> assumption

theorem tensor_entries_dyadic {d e : ℕ} (A : Square d) (B : Square e)
    (hA : ∀ i j, IsDyadic (A i j)) (hB : ∀ i j, IsDyadic (B i j)) :
    ∀ i j, IsDyadic (tensor A B i j) := by
  intro i j
  rw [tensor_apply]
  exact dyadic_mul (hA _ _) (hB _ _)

#print axioms tensor_pair_growth
end NLA.MF12.Paper
