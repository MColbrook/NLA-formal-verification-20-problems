module

public import NLA.MI22.Commuting.JointReduction
public import NLA.MI22.Commuting.PositiveEigenvalue
public import NLA.MI22.Commuting.ScalarMean

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace NLA.MI22.Commuting

theorem commuting_weighted_mean {n : ℕ} (A B : Mat n) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : Commute A B) (t : ℝ) :
    weightedMean A B t = spectralPower A (1-t) * spectralPower B t := by
  apply matrix_eq_of_joint_eigenvectors A B _ _ hA.isHermitian hB.isHermitian hAB
  intro v a b hva hvb
  by_cases hv0 : v = 0
  · simp [hv0]
  have ha := eigenvalue_positive A hA v a hva hv0
  have hb := eigenvalue_positive B hB v b hvb hv0
  have hna := spectralPower_eigenvector A hA v a (-1/2) hva
  have hpa := spectralPower_eigenvector A hA v a (1/2) hva
  have hat := spectralPower_eigenvector A hA v a (1-t) hva
  have hbt := spectralPower_eigenvector B hB v b t hvb
  let C := spectralPower A (-1/2) * B * spectralPower A (-1/2)
  have hC : C.PosDef := sandwich_posDef B _ hB (spectralPower_posDef A hA _)
  have hc : C *ᵥ v = ((a^(-1/2:ℝ)*b*a^(-1/2:ℝ) : ℝ) : ℂ) • v := by
    dsimp only [C]
    simp only [← mulVec_mulVec, hna, hvb, mulVec_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hct := spectralPower_eigenvector C hC v (a^(-1/2:ℝ)*b*a^(-1/2:ℝ)) t hc
  change (spectralPower A (1/2) * spectralPower C t * spectralPower A (1/2)) *ᵥ v = _
  simp only [← mulVec_mulVec, hpa, hct, hat, hbt, mulVec_smul, smul_smul]
  have hs := congrArg Complex.ofReal (scalar_mean_identity a b t ha hb)
  push_cast at hs
  congr 1
  calc
    _ = (↑(a ^ (1 / 2 : ℝ)) : ℂ) * ↑((a ^ (-1 / 2 : ℝ) * b * a ^ (-1 / 2 : ℝ)) ^ t) * ↑(a ^ (1 / 2 : ℝ)) := by ring
    _ = _ := hs.trans (mul_comm _ _)

theorem commuting_left_product {n : ℕ} (A B : Mat n) (hA : A.PosDef) (hB : B.PosDef)
    (hAB : Commute A B) (t : ℝ) : leftProduct A B t = A * B := by
  rw [leftProduct, commuting_weighted_mean A B hA hB hAB t]
  calc
    spectralPower A t * (spectralPower A (1-t) * spectralPower B t) * spectralPower B (1-t) =
        (spectralPower A t * spectralPower A (1-t)) * (spectralPower B t * spectralPower B (1-t)) := by simp only [mul_assoc]
    _ = A * B := by
      rw [← spectralPower_add A hA, ← spectralPower_add B hB,
        show t+(1-t) = 1 by ring, spectralPower_one A hA, spectralPower_one B hB]

#print axioms commuting_weighted_mean
#print axioms commuting_left_product
end NLA.MI22.Commuting
