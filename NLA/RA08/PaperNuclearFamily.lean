module

public import NLA.RA08.PaperNuclearDefinitions
public import NLA.RA08.PaperDerivativeScalar
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearHeight_pos {m : ℕ} (i : Fin m) : 0 < nuclearHeight i := by
  exact pow_pos (by norm_num) _

theorem nuclearHeight_le_quarter {m : ℕ} (i : Fin m) : nuclearHeight i ≤ 1/4 := by
  unfold nuclearHeight
  rw [pow_succ]
  have h : (1/4 : ℝ)^i.val ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

theorem nuclearBaseEntries_pos (m : ℕ) (i : Fin (m+m)) : 0 < nuclearBaseEntries m i := by
  unfold nuclearBaseEntries
  cases h : (finSumFinEquiv (m := m) (n := m)).symm i with
  | inl j => simp only [Sum.elim_inl];have hh := nuclearHeight_le_quarter j;linarith
  | inr j => simp only [Sum.elim_inr];have hh := nuclearHeight_pos j;linarith

theorem nuclearBaseEntries_ne_one (m : ℕ) (i : Fin (m+m)) : nuclearBaseEntries m i ≠ 1 := by
  unfold nuclearBaseEntries
  cases h : (finSumFinEquiv (m := m) (n := m)).symm i with
  | inl j => simp only [Sum.elim_inl];have hh := nuclearHeight_pos j;linarith
  | inr j => simp only [Sum.elim_inr];have hh := nuclearHeight_pos j;linarith

theorem nuclearBase_posDef (m : ℕ) : (nuclearBase m).PosDef :=
  Matrix.posDef_diagonal_iff.mpr (nuclearBaseEntries_pos m)

theorem nuclearPerturbation_posSemidef (m : ℕ) : (nuclearPerturbation m).PosSemidef := by
  have he : nuclearPerturbation m=Matrix.vecMulVec (nuclearUnitVector m) (star (nuclearUnitVector m)) := by
    ext i j
    simp [nuclearPerturbation,Matrix.vecMulVec]
  rw [he]
  exact Matrix.posSemidef_vecMulVec_self_star (nuclearUnitVector m)

theorem nuclearPerturbation_entry (m : ℕ) (i j : Fin (m+m)) :
    nuclearPerturbation m i j=1/(2*m : ℝ) := by
  have hs : (Real.sqrt (2*m : ℝ))^2=2*m := Real.sq_sqrt (by positivity)
  simp only [nuclearPerturbation,nuclearUnitVector]
  rw [← mul_inv,← pow_two,hs,one_div]

theorem nuclearUnitVector_norm_sq (m : ℕ) (hm : 1 ≤ m) :
    ∑ i : Fin (m+m), (nuclearUnitVector m i)^2=1 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m))
  have hentry (i : Fin (m+m)) : (nuclearUnitVector m i)^2=1/(2*m : ℝ) := by
    simpa only [nuclearPerturbation,pow_two] using nuclearPerturbation_entry m i i
  simp only [hentry,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  push_cast
  field_simp
  ring

theorem clipping_below_below (h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    clippingDividedDifference (1-h) (1-k)=1 := by
  rw [clippingDividedDifference_absolute (1-h) (1-k) (by linarith) (by linarith)]
  rw [abs_of_neg (by linarith : 1-h-1 < 0),abs_of_neg (by linarith : 1-k-1 < 0)]
  have hd : -(1-h-1)+ -(1-k-1) ≠ 0 := by linarith
  field_simp
  ring

theorem clipping_above_above (h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    clippingDividedDifference (1+h) (1+k)=0 := by
  rw [clippingDividedDifference_absolute (1+h) (1+k) (by linarith) (by linarith)]
  rw [abs_of_pos (by linarith : 0 < 1+h-1),abs_of_pos (by linarith : 0 < 1+k-1)]
  have hd : (1+h-1)+(1+k-1) ≠ 0 := by linarith
  field_simp
  ring

theorem clipping_below_above (h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    clippingDividedDifference (1-h) (1+k)=h/(h+k) := by
  rw [clippingDividedDifference_absolute (1-h) (1+k) (by linarith) (by linarith)]
  rw [abs_of_neg (by linarith : 1-h-1 < 0),abs_of_pos (by linarith : 0 < 1+k-1)]
  have hd : -(1-h-1)+(1+k-1) ≠ 0 := by linarith
  have hd' : h+k ≠ 0 := by linarith
  field_simp
  ring

theorem clipping_above_below (h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    clippingDividedDifference (1+h) (1-k)=k/(h+k) := by
  rw [clippingDividedDifference_absolute (1+h) (1-k) (by linarith) (by linarith)]
  rw [abs_of_pos (by linarith : 0 < 1+h-1),abs_of_neg (by linarith : 1-k-1 < 0)]
  have hd : (1+h-1)+ -(1-k-1) ≠ 0 := by linarith
  have hd' : h+k ≠ 0 := by linarith
  field_simp
  ring

theorem nuclearDerivative_eq_displayed (m : ℕ) :
    nuclearDerivative m=nuclearDisplayedDerivative m := by
  ext i j
  simp only [nuclearDerivative,clippingDerivative,nuclearPerturbation_entry,
    nuclearDisplayedDerivative,Matrix.smul_apply,smul_eq_mul,Matrix.submatrix_apply,
    nuclearBaseEntries]
  cases hi : (finSumFinEquiv (m := m) (n := m)).symm i with
  | inl p =>
    cases hj : (finSumFinEquiv (m := m) (n := m)).symm j with
    | inl q => simp [clipping_below_below, nuclearHeight_pos]
    | inr q =>
      simp only [Sum.elim_inl,Sum.elim_inr,Matrix.fromBlocks_apply₁₂,nuclearKernel]
      rw [clipping_below_above _ _ (nuclearHeight_pos p) (nuclearHeight_pos q)]
      ring
  | inr p =>
    cases hj : (finSumFinEquiv (m := m) (n := m)).symm j with
    | inl q =>
      simp only [Sum.elim_inl,Sum.elim_inr,Matrix.fromBlocks_apply₂₁,Matrix.transpose_apply,nuclearKernel]
      rw [clipping_above_below _ _ (nuclearHeight_pos p) (nuclearHeight_pos q)]
      rw [add_comm (nuclearHeight p) (nuclearHeight q)]
      ring
    | inr q => simp [clipping_above_above,nuclearHeight_pos]

#print axioms nuclearDerivative_eq_displayed
end NLA.RA08.Paper
