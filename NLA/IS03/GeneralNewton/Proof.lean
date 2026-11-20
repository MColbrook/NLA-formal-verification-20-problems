module

public import NLA.IS03.GeneralNewton.Definitions
public import NLA.IS03.Newton
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open Polynomial
open scoped BigOperators
namespace NLA.IS03.GeneralNewton

theorem coefficient_eq_signed_elementary {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (j : ℕ) :
    coefficient μ j = (-1 : ℂ)^j * elementaryMoments μ j := by
  classical
  by_cases hj : j ≤ Fintype.card ι
  · have h := product_coeff_eq_elementary μ (Nat.sub_le (Fintype.card ι) j)
    simpa only [coefficient, if_pos hj, rootPolynomial, Nat.sub_sub_self hj] using h
  · have he : Finset.powersetCard j (Finset.univ : Finset ι) = ∅ :=
      Finset.powersetCard_eq_empty.mpr (by simpa using (Nat.lt_of_not_ge hj))
    simp [coefficient, hj, elementaryMoments, MvPolynomial.esymm, he]

theorem antidiagonal_sum (k : ℕ) (f : ℕ → ℕ → ℂ) :
    (∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 ∈ Set.Ioo 0 k), f a.1 a.2) =
      ∑ j ∈ Finset.Ico 1 k, f j (k-j) := by
  classical
  rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Finset.sum_filter]
  have hfilter : (Finset.range (k+1)).filter (fun j => j ∈ Set.Ioo 0 k) =
      Finset.Ico 1 k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_Ioo, Finset.mem_Ico]
    omega
  exact congrArg (fun s : Finset ℕ => ∑ j ∈ s, f j (k-j)) hfilter

theorem coefficient_recurrence_all {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (k : ℕ) (hk : 0 < k) :
    powerSum μ k + (∑ j ∈ Finset.Ico 1 k, coefficient μ j * powerSum μ (k-j)) +
      k * coefficient μ k = 0 := by
  rw [← antidiagonal_sum k (fun j t => coefficient μ j * powerSum μ t)]
  simp_rw [coefficient_eq_signed_elementary]
  change powerMoments μ k +
    (∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 ∈ Set.Ioo 0 k),
      (-1 : ℂ)^a.1 * elementaryMoments μ a.1 * powerMoments μ a.2) +
      k * ((-1 : ℂ)^k * elementaryMoments μ k) = 0
  rw [powerMoments_newton μ k hk, pow_succ]
  ring

theorem actual_newton_first_case {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (k : ℕ) (hk : 1 ≤ k) (_hkd : k ≤ Fintype.card ι) :
    powerSum μ k + (∑ j ∈ Finset.Ico 1 k, coefficient μ j * powerSum μ (k-j)) +
      k * coefficient μ k = 0 :=
  coefficient_recurrence_all μ k hk

theorem actual_newton_second_case {ι : Type*} [Fintype ι]
    (μ : ι → ℂ) (k : ℕ) (hk : Fintype.card ι < k) :
    powerSum μ k +
      (∑ j ∈ Finset.Icc 1 (Fintype.card ι), coefficient μ j * powerSum μ (k-j)) = 0 := by
  classical
  have h := coefficient_recurrence_all μ k (by omega)
  have hz : coefficient μ k = 0 := by simp [coefficient, Nat.not_le_of_gt hk]
  rw [hz, mul_zero, add_zero] at h
  have he : (∑ j ∈ Finset.Ico 1 k, coefficient μ j * powerSum μ (k-j)) =
      ∑ j ∈ Finset.Icc 1 (Fintype.card ι), coefficient μ j * powerSum μ (k-j) := by
    symm
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_Icc, Finset.mem_Ico] at hj ⊢
      omega
    · intro j hj hn
      have hgt : Fintype.card ι < j := by
        simp only [Finset.mem_Ico] at hj
        simp only [Finset.mem_Icc, not_and] at hn
        have := hn hj.1
        omega
      simp [coefficient, Nat.not_le_of_gt hgt]
  rw [he] at h
  exact h

#print axioms coefficient_eq_signed_elementary
#print axioms actual_newton_first_case
#print axioms actual_newton_second_case

theorem roots_list_degree (p : ℂ[X]) : p.roots.toList.length = p.natDegree := by
  rw [Multiset.length_toList, ← (IsAlgClosed.splits p).natDegree_eq_card_roots]

theorem roots_list_factor (p : ℂ[X]) (hp : p.Monic) :
    rootPolynomial (fun i : Fin p.roots.toList.length => p.roots.toList[i.1]) = p := by
  rw [rootPolynomial, Fin.prod_univ_fun_getElem p.roots.toList (fun z : ℂ => (X : ℂ[X]) - C z), Multiset.prod_map_toList]
  exact ((IsAlgClosed.splits p).eq_prod_roots_of_monic hp).symm

theorem roots_list_power (p : ℂ[X]) (k : ℕ) :
    powerSum (fun i : Fin p.roots.toList.length => p.roots.toList[i.1]) k =
      (p.roots.map (fun z => z^k)).sum := by
  rw [powerSum, Fin.sum_univ_fun_getElem p.roots.toList (fun z : ℂ => z^k), Multiset.sum_map_toList]

theorem roots_list_coefficient (p : ℂ[X]) (hp : p.Monic) (j : ℕ)
    (hj : j ≤ p.natDegree) :
    coefficient (fun i : Fin p.roots.toList.length => p.roots.toList[i.1]) j =
      p.coeff (p.natDegree-j) := by
  simp only [coefficient, Fintype.card_fin, roots_list_degree, if_pos hj,
    roots_list_factor p hp]

theorem monic_newton_first_case (p : ℂ[X]) (hp : p.Monic)
    (k : ℕ) (hk : 1 ≤ k) (hkd : k ≤ p.natDegree) :
    (p.roots.map (fun z => z^k)).sum +
      (∑ j ∈ Finset.Ico 1 k, p.coeff (p.natDegree-j) *
        (p.roots.map (fun z => z^(k-j))).sum) + k * p.coeff (p.natDegree-k) = 0 := by
  classical
  have h := actual_newton_first_case
    (fun i : Fin p.roots.toList.length => p.roots.toList[i.1]) k hk
    (by simpa only [Fintype.card_fin, roots_list_degree] using hkd)
  simp_rw [roots_list_power] at h
  rw [roots_list_coefficient p hp k hkd] at h
  convert h using 2
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [roots_list_coefficient p hp j (by have := (Finset.mem_Ico.mp hj).2; omega)]

theorem monic_newton_second_case (p : ℂ[X]) (hp : p.Monic)
    (k : ℕ) (hk : p.natDegree < k) :
    (p.roots.map (fun z => z^k)).sum +
      (∑ j ∈ Finset.Icc 1 p.natDegree, p.coeff (p.natDegree-j) *
        (p.roots.map (fun z => z^(k-j))).sum) = 0 := by
  classical
  have h := actual_newton_second_case
    (fun i : Fin p.roots.toList.length => p.roots.toList[i.1]) k
    (by simpa only [Fintype.card_fin, roots_list_degree] using hk)
  simp_rw [roots_list_power, Fintype.card_fin, roots_list_degree] at h
  convert h using 2
  apply Finset.sum_congr rfl
  intro j hj
  rw [roots_list_coefficient p hp j (Finset.mem_Icc.mp hj).2]

#print axioms monic_newton_first_case
#print axioms monic_newton_second_case

end NLA.IS03.GeneralNewton
