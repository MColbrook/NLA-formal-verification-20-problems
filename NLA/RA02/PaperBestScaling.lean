module

public import NLA.RA02.PaperBestIsometricEmbedding

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem frobenius_real_smul {m n : ℕ} (c : ℝ) (A : Matrix (Fin m) (Fin n) ℂ) :
    NLA.RA03.frobeniusSq (c • A)=c^2*NLA.RA03.frobeniusSq A := by
  simp only [NLA.RA03.frobeniusSq,Matrix.smul_apply,Complex.real_smul,
    Complex.normSq_mul,Complex.normSq_ofReal,← Finset.mul_sum,pow_two]

theorem rank_real_smul_le {m n : ℕ} (c : ℝ) (B : Matrix (Fin m) (Fin n) ℂ) :
    (c • B).rank ≤ B.rank := by
  have he : c • B=Matrix.diagonal (fun _ : Fin m => (c : ℂ))*B := by
    ext i j
    simp only [Matrix.smul_apply,Matrix.diagonal_mul,Complex.real_smul]
  rw [he]
  exact Matrix.rank_mul_le_right _ _

theorem rectangularBest_real_smul {m n : ℕ} (c : ℝ) (A : Matrix (Fin m) (Fin n) ℂ)
    (r : ℕ) : rectangularBestRankErrorSquared (c • A) r = c^2*rectangularBestRankErrorSquared A r := by
  by_cases hc : c=0
  · subst c
    simp only [zero_smul,zero_pow (by omega : 2 ≠ 0),zero_mul]
    rw [rectangularBest_eq_gramTail,gramTail_zero]
  · apply le_antisymm
    · obtain ⟨B,hB,he⟩ := rectangular_best_error_attained A r
      have hRank : (c • B).rank ≤ r := (rank_real_smul_le c B).trans hB
      have hb := rectangularBest_le_candidate (c • A) (c • B) r hRank
      rw [← smul_sub,frobenius_real_smul,he,← rectangularBest_eq_gramTail] at hb
      exact hb
    · obtain ⟨D,hD,he⟩ := rectangular_best_error_attained (c • A) r
      have hRank : ((c⁻¹ : ℝ) • D).rank ≤ r := (rank_real_smul_le c⁻¹ D).trans hD
      have hErr : A-(c⁻¹ : ℝ) • D=(c⁻¹ : ℝ) • (c • A-D) := by
        rw [smul_sub,smul_smul,inv_mul_cancel₀ hc,one_smul]
      have hb := rectangularBest_le_candidate A ((c⁻¹ : ℝ) • D) r hRank
      rw [hErr,frobenius_real_smul,he,← rectangularBest_eq_gramTail] at hb
      have hs := mul_le_mul_of_nonneg_left hb (sq_nonneg c)
      calc
        c^2*rectangularBestRankErrorSquared A r ≤
            c^2*((c⁻¹)^2*rectangularBestRankErrorSquared (c • A) r) := hs
        _ = rectangularBestRankErrorSquared (c • A) r := by
          rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ hc,one_pow,one_mul]

#print axioms rectangularBest_real_smul
end NLA.RA02.Paper
