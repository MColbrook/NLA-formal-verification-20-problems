module

public import NLA.TR27.PaperProjectedBorder

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

/-- The complete algebraic and rank components for the literal paper family.
Smooth rational embedding is a separate, still outstanding geometric statement. -/
theorem family_algebraic_rank_data (r m : ℕ) (hr : 3 ≤ r) (hm : 2 ≤ m) :
    ∃ E : QuotientSpace (familyDegree r m) r (chosenParameters r) ≃ₗ[ℂ]
        (Fin (familyDegree r m) → ℂ),
      ∃ hD : 2 ≤ familyDegree r m,
      (∀ w, E (quotientProjection (familyDegree r m) r (chosenParameters r) w) =
        coordinateProjection (familyDegree r m) r hD w) ∧
      (ProjectiveVariety.mk (familyDegree r m) E (imageIdeal (familyDegree r m) r hD)).Admissible ∧
      (ProjectiveVariety.mk (familyDegree r m) E (imageIdeal (familyDegree r m) r hD)).points =
        quotientPoints (familyDegree r m) r (chosenParameters r) ∧
      (∃ hv : quotientTangent (familyDegree r m) r (chosenParameters r) ≠ 0,
        borderRank (ProjectiveVariety.mk (familyDegree r m) E (imageIdeal (familyDegree r m) r hD))
          (Projectivization.mk ℂ _ hv) = 2 ∧
        projectiveRank (quotientPoints (familyDegree r m) r (chosenParameters r))
          (Projectivization.mk ℂ _ hv) = r ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ m →
          projectiveRank (productPoints (quotientPoints (familyDegree r m) r (chosenParameters r)) k)
            (powerPoint (Projectivization.mk ℂ _ hv) k) = r^k) := by
  have hg := family_degree_gap hr hm
  have hD : 2 ≤ familyDegree r m := by omega
  obtain ⟨hv, hmin, hb⟩ := projected_tangent_border_two (familyDegree r m) r hD hr hg
  refine ⟨quotientCoordinateEquiv (familyDegree r m) r hD hr, hD,
    quotientCoordinateEquiv_projection (familyDegree r m) r hD hr,
    quotient_image_admissible (familyDegree r m) r hD hr,
    quotient_image_points (familyDegree r m) r hD hr, hv, hb, ?_, ?_⟩
  · exact (quotient_tangent_rank (by omega : 1 ≤ familyDegree r m) (by omega : 1 ≤ r)
      hg (chosenParameters r) (chosenParameters_injective r)).csInf_eq
  · intro k hk hkm
    obtain ⟨hv', hpow⟩ := family_tensor_rank hr hm hkm
    exact hpow.csInf_eq

#print axioms family_algebraic_rank_data
end NLA.TR27.Paper
