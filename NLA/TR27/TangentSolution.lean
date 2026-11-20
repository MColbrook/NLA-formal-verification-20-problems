module

public import NLA.TR27.PaperTangent

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

theorem paper_tangent_rank (D : ℕ) (hD : 2 ≤ D) :
    projectiveRank (curvePoints D) (tangentPoint D hD) = D := by
  exact rational_normal_tangent_rank D hD

theorem paper_tangent_lower (D : ℕ) (hD : 2 ≤ D) (k : ℕ) (hk : k < D) :
    ¬ ProjectiveRankAtMost (curvePoints D) k (tangentPoint D hD) := by
  exact tangent_projective_lower D (by omega) k hk

theorem paper_tangent_decomposition (D : ℕ) (hD : 2 ≤ D) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ D) :
    tangentVector D = ∑ i : Fin D,
      ((D : ℂ)⁻¹ * (ζ ^ (D-1)) ^ (i : ℕ)) • curveVector D (some (ζ ^ (i : ℕ))) := by
  exact tangent_root_decomposition hD hζ

#print axioms paper_tangent_rank
#print axioms paper_tangent_lower
#print axioms paper_tangent_decomposition

end NLA.TR27.Paper
