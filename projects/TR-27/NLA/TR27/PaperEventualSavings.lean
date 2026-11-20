module

public import NLA.TR27.PaperSecantRootAverage
public import NLA.TR27.PaperTensorMixture
public import NLA.TR27.PaperEventualPowerBound
public import NLA.TR27.PaperQuotientRank

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical TensorProduct LinearAlgebra.Projectivization
open Filter
namespace NLA.TR27.Paper

theorem quotient_tangent_power_upper (D r : ℕ) (hD : 1 ≤ D) (hgap : 1+r < D)
    (hv : quotientTangent D r (chosenParameters r) ≠ 0) (k : ℕ) :
    ProjectiveRankAtMost (productPoints (quotientPoints D r (chosenParameters r)) k)
      ((k*(D-1)+1)*2^k) (powerPoint (Projectivization.mk ℂ _ hv) k) := by
  let L := k*(D-1)+1
  let ζ : ℂ := Complex.exp (2*Real.pi*Complex.I / L)
  have hζ : IsPrimitiveRoot ζ L := Complex.isPrimitiveRoot_exp L (by dsimp [L]; omega)
  let t : Fin L → ℂ := fun l => ζ^l.val
  have ht (l : Fin L) : t l ≠ 0 := pow_ne_zero _ (hζ.ne_zero (by dsimp [L]; omega))
  let w : Fin L → Fin 2 → QuotientSpace D r (chosenParameters r) :=
    fun l => ![quotientCurve D r (chosenParameters r) (some (t l)),
      quotientCurve D r (chosenParameters r) (some 0)]
  have hw (l : Fin L) (j : Fin 2) : w l j ≠ 0 := by
    fin_cases j <;> exact quotient_curve_nonzero hD hgap _ _
  let q := fun l j => Projectivization.mk ℂ (w l j) (hw l j)
  apply projective_power_mixture_upper _ _ _ (represents_mk _ hv) L 2 k
    (fun l => projectedSecant D r (t l)) w
    (fun l => ![(t l)⁻¹,-(t l)⁻¹]) (fun _ => (L : ℂ)⁻¹) q
  · intro l j
    exact represents_mk _ _
  · intro l j
    fin_cases j
    · exact ⟨some (t l), represents_mk _ _⟩
    · exact ⟨some 0, represents_mk _ _⟩
  · intro l
    rw [projectedSecant_difference D r (t l) (ht l)]
    simp [w, Fin.sum_univ_two, sub_eq_add_neg]
  · rw [← Finset.smul_sum]
    exact (projectedSecant_tensor_root_average D r k hζ).symm

/-- An explicit spanning witness establishes a nonempty rank set before
taking its minimum. -/
theorem quotient_tangent_power_rank_upper (D r : ℕ) (hD : 1 ≤ D) (hgap : 1+r < D)
    (hv : quotientTangent D r (chosenParameters r) ≠ 0) (k : ℕ) :
    projectiveRank (productPoints (quotientPoints D r (chosenParameters r)) k)
      (powerPoint (Projectivization.mk ℂ _ hv) k) ≤ (k*(D-1)+1)*2^k := by
  exact csInf_le (OrderBot.bddBelow _)
    (quotient_tangent_power_upper D r hD hgap hv k)

theorem quotient_tangent_eventual_saving (D r : ℕ) (hD : 1 ≤ D) (hr : 2 < r)
    (hgap : 1+r < D) (hv : quotientTangent D r (chosenParameters r) ≠ 0) :
    ∀ᶠ k : ℕ in atTop,
      projectiveRank (productPoints (quotientPoints D r (chosenParameters r)) k)
        (powerPoint (Projectivization.mk ℂ _ hv) k) < r^k := by
  filter_upwards [eventual_power_bound D r hr] with k hk
  exact lt_of_le_of_lt (quotient_tangent_power_rank_upper D r hD hgap hv k) hk

theorem family_eventual_saving (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    ∃ hv : quotientTangent (familyDegree r m) r (chosenParameters r) ≠ 0,
      (∀ k : ℕ, ProjectiveRankAtMost
        (productPoints (quotientPoints (familyDegree r m) r (chosenParameters r)) k)
        ((k*(familyDegree r m-1)+1)*2^k) (powerPoint (Projectivization.mk ℂ _ hv) k)) ∧
      (∀ᶠ k : ℕ in atTop,
        projectiveRank (productPoints (quotientPoints (familyDegree r m) r (chosenParameters r)) k)
          (powerPoint (Projectivization.mk ℂ _ hv) k) < r^k) := by
  have hgap := family_degree_gap hr hm
  have hv := quotient_tangent_nonzero (by omega : 1 ≤ familyDegree r m) (by omega : 1 ≤ r)
    (by omega : r+r < familyDegree r m) (chosenParameters r) (chosenParameters_injective r)
  exact ⟨hv, quotient_tangent_power_upper _ r (by omega) (by omega) hv,
    quotient_tangent_eventual_saving _ r (by omega) (by omega) (by omega) hv⟩

theorem explicit_thirteenth_power_saving :
    ∃ hv : quotientTangent 12 3 (chosenParameters 3) ≠ 0,
      projectiveRank (productPoints (quotientPoints 12 3 (chosenParameters 3)) 13)
        (powerPoint (Projectivization.mk ℂ _ hv) 13) ≤ 144*2^13 ∧
      projectiveRank (productPoints (quotientPoints 12 3 (chosenParameters 3)) 13)
        (powerPoint (Projectivization.mk ℂ _ hv) 13) < 3^13 := by
  have hv := quotient_tangent_nonzero (by norm_num : 1 ≤ 12) (by norm_num : 1 ≤ 3)
    (by norm_num : 3+3 < 12) (chosenParameters 3) (chosenParameters_injective 3)
  have hu := quotient_tangent_power_rank_upper 12 3 (by norm_num) (by norm_num) hv 13
  exact ⟨hv, hu, lt_of_le_of_lt hu explicit_thirteenth_power_saving_bound⟩

/-- For each prescribed cutoff there is a curve with no saving through that
cutoff, but with strict savings at every sufficiently large power. -/
theorem savings_delay_unbounded (N : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ N ≤ m ∧
      ∃ hv : quotientTangent (familyDegree 3 m) 3 (chosenParameters 3) ≠ 0,
        (∀ k : ℕ, 1 ≤ k → k ≤ N →
          projectiveRank (productPoints (quotientPoints (familyDegree 3 m) 3 (chosenParameters 3)) k)
            (powerPoint (Projectivization.mk ℂ _ hv) k) = 3^k) ∧
        (∀ᶠ k : ℕ in atTop,
          projectiveRank (productPoints (quotientPoints (familyDegree 3 m) 3 (chosenParameters 3)) k)
            (powerPoint (Projectivization.mk ℂ _ hv) k) < 3^k) := by
  obtain ⟨hv, hu, he⟩ := family_eventual_saving 3 (N+2) (by omega) (by omega)
  refine ⟨N+2, by omega, by omega, hv, ?_, he⟩
  intro k hk hkN
  obtain ⟨hv', hmin⟩ := family_tensor_rank (by omega : 3 ≤ 3)
    (by omega : 2 ≤ N+2) (by omega : k ≤ N+2)
  exact hmin.csInf_eq

#print axioms savings_delay_unbounded
#print axioms family_eventual_saving
#print axioms explicit_thirteenth_power_saving
end NLA.TR27.Paper
