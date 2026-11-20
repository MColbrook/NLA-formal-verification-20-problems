module

public import NLA.IV04.RationalRecessionReplayR3.PureDefinitions
/- Feasibility at unbounded thresholds forces actual recession coefficients. -/
public import NLA.IV04.RationalRecessionReplayR3.RationalRecession.Recurrence

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04RationalRecessionRay
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment

theorem unbounded_nat_affine_coefficient_nonpositive
    (S : ℕ → Prop) (hS : ∀ K, ∃ k, K ≤ k ∧ S k)
    (u v C : ℝ) (hineq : ∀ k, S k → u+(k : ℝ)*v ≤ C) : v ≤ 0 := by
  by_contra hn
  have hv : 0 < v := lt_of_not_ge hn
  obtain ⟨N,hN⟩ := exists_nat_gt ((C-u)/v)
  obtain ⟨k,hNk,hk⟩ := hS N
  have hcast : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hNk
  have hratio : (C-u)/v < (k : ℝ) := hN.trans_le hcast
  have hprod := (div_lt_iff₀ hv).mp hratio
  have hb := hineq k hk
  linarith

theorem affine_feasible_points_yield_recession
    {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (u r : Fin n → ℝ)
    (S : ℕ → Prop) (hS : ∀ K, ∃ k, K ≤ k ∧ S k)
    (hfeas : ∀ k, S k → feasible A b (u+(k : ℝ) • r)) :
    ∀ i, (A *ᵥ r) i ≤ 0 := by
  intro i
  apply unbounded_nat_affine_coefficient_nonpositive S hS ((A *ᵥ u) i) ((A *ᵥ r) i) (b i)
  intro k hk
  simpa only [mulVec_shift] using hfeas k hk i

theorem affine_thresholds_yield_positive_objective
    {n : ℕ} (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (u r : Fin n → ℝ)
    (S : ℕ → Prop) (hS : ∀ K, ∃ k, K ≤ k ∧ S k)
    (hcost : ∀ k, S k → (k : ℝ) ≤ ℓ (u+(k : ℝ) • r)) : 1 ≤ ℓ r := by
  have hcoeff : 1-ℓ r ≤ 0 := by
    apply unbounded_nat_affine_coefficient_nonpositive S hS 0 (1-ℓ r) (ℓ u)
    intro k hk
    have hc := hcost k hk
    rw [objective_shift] at hc
    nlinarith
  linarith

theorem recession_direction_feasible_ray
    {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ) (x r : Fin n → ℝ)
    (hx : feasible A b x) (hr : ∀ i, (A *ᵥ r) i ≤ 0) :
    ∀ t : ℝ, 0 ≤ t → feasible A b (x+t • r) := by
  intro t ht i
  rw [mulVec_shift]
  exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht (hr i))).trans (hx i)

#print axioms unbounded_nat_affine_coefficient_nonpositive
#print axioms affine_feasible_points_yield_recession
#print axioms affine_thresholds_yield_positive_objective
#print axioms recession_direction_feasible_ray
end
end Reference.IV04RationalRecessionRay
