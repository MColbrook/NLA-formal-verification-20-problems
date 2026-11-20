module

public import NLA.IV04.PolyhedronSupportReplayR3.PureDefinitions
/- Actual linear objectives and bounded recession directions; original constraints only. -/
public import NLA.IV04.PolyhedronSupportReplayR3.AffinePolyhedronSteps.Extreme

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04OriginalObjectiveAttainment
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps

theorem objective_shift {n : ℕ} (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (x d : Fin n → ℝ) (t : ℝ) : ℓ (x+t • d)=ℓ x+t*ℓ d := by
  simp

theorem positive_objective_has_positive_row
    {ι : Type*} [Fintype ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℝ) (b : ι → ℝ)
    (ℓ : (Fin n → ℝ) →ₗ[ℝ] ℝ) (B : ℝ) (x d : Fin n → ℝ)
    (hx : feasible A b x) (hpos : 0 < ℓ d)
    (hB : ∀ y, feasible A b y → ℓ y ≤ B) : ∃ i, 0 < (A *ᵥ d) i := by
  classical
  by_contra hn
  have hd : ∀ i, (A *ᵥ d) i ≤ 0 := by simpa only [not_exists,not_lt] using hn
  let t := (B-ℓ x+1)/ℓ d
  have hBx := hB x hx
  have ht : 0 < t := div_pos (by linarith) hpos
  have hy : feasible A b (x+t • d) := by
    intro i
    rw [mulVec_shift]
    exact (add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos ht.le (hd i))).trans (hx i)
  have hvalue : ℓ (x+t • d)=B+1 := by
    rw [objective_shift]
    dsimp [t]
    rw [div_mul_cancel₀ _ hpos.ne']
    ring
  have hbnd := hB (x+t • d) hy
  rw [hvalue] at hbnd
  linarith

#print axioms objective_shift
#print axioms positive_objective_has_positive_row
end
end Reference.IV04OriginalObjectiveAttainment
