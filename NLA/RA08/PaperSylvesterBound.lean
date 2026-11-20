module

public import NLA.RA08.PaperAbsoluteFrobenius
public import NLA.RA08.PaperAbsoluteIdentities
public import NLA.RA08.PaperSylvesterAlgebra

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix.Norms.Frobenius
namespace NLA.RA08.Paper

theorem diagonalSylvesterInverse_frobenius_bound {n : ℕ} (a : Fin n → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F : RealMatrix n,
      frobeniusNorm (diagonalSylvesterInverse a F) ≤ K*frobeniusNorm F := by
  let S : ℝ := ∑ i, ∑ j, ((a i+a j)⁻¹)^2
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  refine ⟨Real.sqrt S,Real.sqrt_nonneg _,?_⟩
  intro F
  have hc (i j : Fin n) : ((a i+a j)⁻¹)^2 ≤ S := by
    calc
      _ ≤ ∑ j, ((a i+a j)⁻¹)^2 := Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ S := by
        dsimp [S]
        exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => sq_nonneg ((a k+a l)⁻¹)) (Finset.mem_univ i)
  have hs : frobeniusSquared (diagonalSylvesterInverse a F) ≤ S*frobeniusSquared F := by
    unfold frobeniusSquared
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    change (F i j/(a i+a j))^2 ≤ S*(F i j)^2
    calc
      _ = ((a i+a j)⁻¹)^2*(F i j)^2 := by rw [div_eq_mul_inv];ring
      _ ≤ S*(F i j)^2 := mul_le_mul_of_nonneg_right (hc i j) (sq_nonneg _)
  rw [frobeniusSquared_norm,frobeniusSquared_norm] at hs
  have hr : (Real.sqrt S*frobeniusNorm F)^2=S*frobeniusNorm F^2 := by
    rw [mul_pow,Real.sq_sqrt hS]
  rw [← hr] at hs
  exact (sq_le_sq₀ (frobeniusNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (frobeniusNorm_nonneg _))).mp hs

theorem sylvester_quadratic_remainder_bound {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (M E : RealMatrix n)
    (hM : M.IsHermitian) (h0 : matrixAbsolute M=Matrix.diagonal a)
    (hE : E.IsHermitian) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      frobeniusNorm (matrixAbsolute (M+t • E)-Matrix.diagonal a-
        t • diagonalSylvesterInverse a (M*E+E*M)) ≤ C*t^2 := by
  obtain ⟨K,hK,hKF⟩ := diagonalSylvesterInverse_frobenius_bound a
  refine ⟨2*K*frobeniusNorm E^2,by positivity,?_⟩
  intro t
  have htH : (M+t • E).IsHermitian := hM.add (hE.smul (by simp [IsSelfAdjoint]))
  have hbase : Matrix.diagonal a*Matrix.diagonal a=M*M := by
    rw [← h0]
    exact matrixAbsolute_square M hM
  have htSq := matrixAbsolute_square (M+t • E) htH
  let D := matrixAbsolute (M+t • E)-Matrix.diagonal a
  have hD : frobeniusNorm D ≤ |t| * frobeniusNorm E := by
    have hb := matrixAbsolute_frobenius_nonexpansive (M+t • E) M htH hM
    rw [h0,add_sub_cancel_left] at hb
    simpa only [frobeniusNorm,norm_smul,Real.norm_eq_abs] using hb
  rw [sylvester_remainder_identity a ha M E (matrixAbsolute (M+t • E)) t hbase htSq]
  calc
    _ ≤ K*frobeniusNorm (t^2 • (E*E)-D*D) := hKF _
    _ ≤ K*(t^2*frobeniusNorm (E*E)+frobeniusNorm (D*D)) := by
      apply mul_le_mul_of_nonneg_left _ hK
      have hn := norm_sub_le (t^2 • (E*E)) (D*D)
      simpa only [frobeniusNorm,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg t)] using hn
    _ ≤ K*(t^2*(frobeniusNorm E*frobeniusNorm E)+(|t| * frobeniusNorm E)^2) := by
      apply mul_le_mul_of_nonneg_left _ hK
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (Matrix.frobenius_norm_mul E E) (sq_nonneg t)
      · exact (Matrix.frobenius_norm_mul D D).trans (by
          simpa only [frobeniusNorm,pow_two] using mul_self_le_mul_self (frobeniusNorm_nonneg D) hD)
    _ = (2*K*frobeniusNorm E^2)*t^2 := by rw [mul_pow,sq_abs];ring

end NLA.RA08.Paper
