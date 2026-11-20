module

public import NLA.IV04.RationalRecessionReplayR3.PureDefinitions
/- Genuine linearity of the actual original-mask Cramer candidate in its RHS. -/
public import NLA.IV04.RationalRecessionReplayR3.RationalRecession.Affine

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04RationalRecessionRay
noncomputable section
open scoped Matrix
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment

theorem cramerCandidate_affine {n : ℕ} (G : Matrix (Fin n) (Fin n) ℚ)
    (c₀ c₁ : Fin n → ℚ) (k : ℚ) :
    cramerCandidate G (c₀+k • c₁)=cramerCandidate G c₀+k • cramerCandidate G c₁ := by
  funext j
  simp only [cramerCandidate,map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

theorem originalMaskCandidate_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (A : Matrix ι (Fin n) ℚ) (b₀ b₁ : ι → ℚ) (I : Finset ι) (k : ℚ) :
    originalMaskCandidate A (b₀+k • b₁) I=
      originalMaskCandidate A b₀ I+k • originalMaskCandidate A b₁ I := by
  have hmask : maskedBounds (b₀+k • b₁) I=maskedBounds b₀ I+k • maskedBounds b₁ I := by
    funext i
    by_cases hi : i ∈ I <;> simp [maskedBounds,hi]
  unfold originalMaskCandidate
  rw [hmask,Matrix.mulVec_add,Matrix.mulVec_smul,cramerCandidate_affine]

theorem realVector_rational_affine {n : ℕ} (u r : Fin n → ℚ) (k : ℚ) :
    realVector (u+k • r)=realVector u+(k : ℝ) • realVector r := by
  funext j
  simp [realVector]

#print axioms cramerCandidate_affine
#print axioms originalMaskCandidate_affine
#print axioms realVector_rational_affine
end
end Reference.IV04RationalRecessionRay
