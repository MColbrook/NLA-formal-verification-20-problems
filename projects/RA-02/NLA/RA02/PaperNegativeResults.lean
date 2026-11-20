module

public import NLA.RA02.PaperMainLimits
public import NLA.RA02.PaperExponentialGrowth

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Topology ComplexOrder
open Filter
namespace NLA.RA02.Paper

theorem best_family_error_positive (r : ℕ) {t : ℝ} (ht : 0 < t) :
    0 < bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r := by
  rw [bestRankErrorSquared_eq_tail r _ (complexify_posDef _ (sharpFamily_posDef _ _ ht))]
  change 0 < familySingularTailSquared r t
  rw [familySingularTailSquared_eq r ht]
  exact sq_pos_of_pos (familyRankTail_positive r ht)

theorem cholesky_factor_counterexample (r : ℕ) (c : ℝ) (hc : c < (2 : ℝ)^r) :
    ∃ t : ℝ, 0 < t ∧
      c * familyRankTail r t < NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) t)) r := by
  have he := (sharp_cholesky_rankTail_limit r).eventually (eventually_gt_nhds hc)
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hb⟩ := (hp.and he).exists
  exact ⟨t,ht,(lt_div_iff₀ (familyRankTail_positive r ht)).mp hb⟩

theorem lu_factor_counterexample (r : ℕ) (c : ℝ) (hc : c < (4 : ℝ)^r) :
    ∃ t : ℝ, 0 < t ∧
      c * bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r <
        NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r := by
  have he := (sharp_lu_bestApprox_limit r).eventually (eventually_gt_nhds hc)
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hb⟩ := (hp.and he).exists
  exact ⟨t,ht,(lt_div_iff₀ (best_family_error_positive r ht)).mp hb⟩

theorem cholesky_real_power_counterexample (C p : ℝ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ t : ℝ, 0 < t ∧
      C * Real.rpow r p * familyRankTail r t <
        NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) t)) r := by
  obtain ⟨r,hr,hc⟩ := real_power_exponential_gap C p
  exact ⟨r,hr,cholesky_factor_counterexample r _ hc⟩

theorem lu_polynomial_counterexample (q : Polynomial ℝ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ t : ℝ, 0 < t ∧
      q.eval (r : ℝ) * (2 : ℝ)^r * bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r <
        NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r := by
  obtain ⟨r,hr,hc⟩ := polynomial_exponential_gap q
  exact ⟨r,hr,lu_factor_counterexample r _ hc⟩

theorem lu_constant_counterexample (C : ℝ) :
    ∃ r : ℕ, 1 ≤ r ∧ ∃ t : ℝ, 0 < t ∧
      C * (2 : ℝ)^r * bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r <
        NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r := by
  simpa using lu_polynomial_counterexample (Polynomial.C C)

theorem no_uniform_polynomial_cholesky_factor : ¬ NLA.RA02.PolynomialTraceFactor := by
  rintro ⟨C,hC,p,hp,hbound⟩
  obtain ⟨r,hr,t,ht,hbad⟩ := cholesky_real_power_counterexample C p
  have hA := complexify_posDef _ (sharpFamily_posDef (r+1) t ht)
  have hb := hbound (r+1) (by omega) _ hA.posSemidef r hr (Nat.le_succ r)
  have he : familyRankTail r t = NLA.RA02.rankTail _ hA.isHermitian r := by
    simp only [familyRankTail, dif_pos hA.isHermitian]
  rw [he] at hbad
  exact (not_lt_of_ge hb) hbad

theorem no_uniform_polynomial_lu_factor :
    ¬ ∃ q : Polynomial ℝ, ∀ n : ℕ, ∀ A : NLA.RA02.Square n, ∀ r : ℕ,
      1 ≤ r → r ≤ n → NLA.RA03.expectedError A r ≤
        q.eval (r : ℝ) * (2 : ℝ)^r * bestRankErrorSquared A r := by
  rintro ⟨q,hbound⟩
  obtain ⟨r,hr,t,ht,hbad⟩ := lu_polynomial_counterexample q
  exact (not_lt_of_ge (hbound (r+1) _ r hr (Nat.le_succ r))) hbad

#print axioms lu_polynomial_counterexample
end NLA.RA02.Paper
