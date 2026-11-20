module

public import NLA.RA02.PaperFrobeniusIsometry

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem rectangularBest_le_candidate {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ)
    (r : ℕ) (hB : B.rank ≤ r) :
    rectangularBestRankErrorSquared A r ≤ NLA.RA03.frobeniusSq (A-B) := by
  rw [rectangularBest_eq_gramTail]
  exact gramTail_le_lowRankError A B r hB

theorem rectangularBest_isometric_embedding {n N : ℕ}
    (P : Matrix (Fin N) (Fin n) ℂ) (hP : P.conjTranspose*P=1)
    (A : NLA.RA02.Square n) (r : ℕ) :
    rectangularBestRankErrorSquared (P*A*P.conjTranspose) r =
      rectangularBestRankErrorSquared A r := by
  let C := P*A*P.conjTranspose
  apply le_antisymm
  · obtain ⟨B,hB,he⟩ := rectangular_best_error_attained A r
    have hRank : (P*B*P.conjTranspose).rank ≤ r :=
      (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hB)
    have hErr : C-P*B*P.conjTranspose=P*(A-B)*P.conjTranspose := by
      dsimp [C]
      rw [Matrix.mul_sub,Matrix.sub_mul]
    have hb := rectangularBest_le_candidate C (P*B*P.conjTranspose) r hRank
    rw [hErr,frobenius_isometric_embedding P hP,he,← rectangularBest_eq_gramTail] at hb
    exact hb
  · obtain ⟨D,hD,he⟩ := rectangular_best_error_attained C r
    have hRank : (P.conjTranspose*D*P).rank ≤ r :=
      (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hD)
    have hRecover : P.conjTranspose*C*P=A := by
      dsimp [C]
      calc
        _ = (P.conjTranspose*P)*A*(P.conjTranspose*P) := by simp only [Matrix.mul_assoc]
        _ = A := by rw [hP,Matrix.one_mul,Matrix.mul_one]
    have hErr : P.conjTranspose*(C-D)*P=A-P.conjTranspose*D*P := by
      rw [Matrix.mul_sub,Matrix.sub_mul,hRecover]
    have hb := rectangularBest_le_candidate A (P.conjTranspose*D*P) r hRank
    rw [← hErr] at hb
    have hc := frobenius_double_compression_le P hP (C-D)
    rw [he,← rectangularBest_eq_gramTail] at hc
    exact hb.trans hc

#print axioms rectangularBest_isometric_embedding
end NLA.RA02.Paper
