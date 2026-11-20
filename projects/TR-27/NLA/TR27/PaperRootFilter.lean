module

public import NLA.TR27.PaperTangent

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

theorem root_sum_low_degree {L : ℕ} (hL : 0 < L) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ L) (j : ℕ) (hj : j < L) :
    (∑ a : Fin L, (ζ^(a.val))^j) = if j = 0 then (L : ℂ) else 0 := by
  by_cases hj0 : j = 0
  · simp [hj0]
  · rw [if_neg hj0]
    have he (a : Fin L) : (ζ^a.val)^j = (ζ^j)^a.val := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
    simp_rw [he]
    rw [Fin.sum_univ_eq_sum_range]
    have hne : ζ^j ≠ 1 := by
      intro hz
      have hdiv := (hζ.pow_eq_one_iff_dvd j).mp hz
      exact (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hj0) hj) hdiv
    have hp : (ζ^j)^L = 1 := by
      rw [← pow_mul, Nat.mul_comm j L, pow_mul, hζ.pow_eq_one, one_pow]
    have h := geom_sum_mul (ζ^j) L
    rw [hp, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)

/-- Roots of unity extract the constant coefficient of any finite
vector-valued sum with exponents strictly below L. -/
theorem root_average_terms {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ι : Type*} [Fintype ι] {L : ℕ} (hL : 0 < L) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ L)
    (e : ι → ℕ) (he : ∀ i, e i < L) (b : ι → V) :
    (L : ℂ)⁻¹ • (∑ a : Fin L, ∑ i : ι, (ζ^a.val)^(e i) • b i) =
      ∑ i : ι, (0 : ℂ)^(e i) • b i := by
  rw [Finset.sum_comm, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_smul, root_sum_low_degree hL hζ (e i) (he i)]
  by_cases hi : e i = 0
  · simp [hi, smul_smul, Nat.cast_ne_zero.mpr (Nat.ne_of_gt hL)]
  · simp [hi]

#print axioms root_average_terms
end NLA.TR27.Paper
