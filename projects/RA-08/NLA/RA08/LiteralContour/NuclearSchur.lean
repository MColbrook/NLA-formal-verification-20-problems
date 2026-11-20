module

public import NLA.RA08.LiteralContour.NuclearDefinitions
public import NLA.RA08.PaperNuclearSmallest
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical Matrix BigOperators MatrixOrder

namespace NLA.RA08.Paper.LiteralContour

theorem small_tail_block_lower (m : ℕ) (η t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/4) :
    (smallTailBlock m η t-(1/2 : ℝ) • 1).PosSemidef := by
  have ha : nuclearLiftSmallest m η t ≤ 1/4 := by
    have h := nuclearLiftSmallest_upper m η t hη1
    nlinarith
  have hd : (diagonal (fun i => nuclearBaseEntries m i-
      nuclearLiftSmallest m η t-1/2)).PosSemidef := by
    apply posSemidef_diagonal_iff.mpr
    intro i
    linarith [nuclearBaseEntries_lower m i]
  have hp := (nuclearPerturbation_posSemidef m).smul (mul_nonneg ht0 hη0)
  convert hd.add hp using 1
  ext i j
  simp only [smallTailBlock,nuclearBase,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,smul_eq_mul,diagonal_apply,Matrix.one_apply]
  split_ifs <;> ring

theorem small_tail_block_posDef (m : ℕ) (η t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/4) :
    (smallTailBlock m η t).PosDef := by
  have hd : ((1/2 : ℝ) • (1 : RealMatrix (m+m))).PosDef := by
    convert (posDef_diagonal_iff.mpr (fun _ : Fin (m+m) =>
      (by norm_num : (0 : ℝ) < 1/2))) using 1
    ext i j
    simp [diagonal_apply,Matrix.one_apply]
  have h := hd.add_posSemidef (small_tail_block_lower m η t hη0 hη1 ht0 ht1)
  simpa only [add_sub_cancel] using h

theorem nuclear_eigenvector_prefix (m : ℕ) (η t a : ℝ) (hη : 0 ≤ η)
    (x : Fin (m+m+1) → ℝ) (he : nuclearLiftA m η t *ᵥ x = a • x) :
    (nuclearBase m+(t*η) • nuclearPerturbation m-a • 1) *ᵥ
      (fun i => x i.castSucc) =
      (-(t*Real.sqrt η*Real.sqrt (1-η)*x (Fin.last (m+m)))) • nuclearUnitVector m := by
  ext i
  have h := congrFun he i.castSucc
  simp only [nuclearLiftA,Matrix.add_mulVec,Matrix.smul_mulVec,nuclearLiftPerturbation,
    nuclear_real_outer_mulVec,nuclearLiftBase,Matrix.mulVec_diagonal,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,nuclearLiftBaseEntries,Fin.snoc_castSucc,
    nuclearLiftVector_dot] at h
  simp only [nuclearLiftVector,Fin.snoc_castSucc] at h
  have hs := Real.sq_sqrt hη
  have hp : nuclearPerturbation m = Matrix.vecMulVec (nuclearUnitVector m)
      (nuclearUnitVector m) := rfl
  simp only [Matrix.sub_mulVec,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    nuclearBase,Matrix.mulVec_diagonal,hp,nuclear_real_outer_mulVec,
    Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  linear_combination h - t*nuclearUnitVector m i*
    (nuclearUnitVector m ⬝ᵥ (fun i => x i.castSucc))*hs

theorem nuclear_eigenvector_last (m : ℕ) (η t a : ℝ) (hη : η ≤ 1)
    (x : Fin (m+m+1) → ℝ) (he : nuclearLiftA m η t *ᵥ x = a • x) :
    a*x (Fin.last (m+m)) = t*Real.sqrt η*Real.sqrt (1-η)*
      (nuclearUnitVector m ⬝ᵥ (fun i => x i.castSucc))+
      t*(1-η)*x (Fin.last (m+m)) := by
  have h := congrFun he (Fin.last (m+m))
  simp only [nuclearLiftA,Matrix.add_mulVec,Matrix.smul_mulVec,nuclearLiftPerturbation,
    nuclear_real_outer_mulVec,nuclearLiftBase,Matrix.mulVec_diagonal,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul,nuclearLiftBaseEntries,Fin.snoc_last,
    nuclearLiftVector_dot,zero_mul,zero_add] at h
  simp only [nuclearLiftVector,Fin.snoc_last] at h
  have hs := Real.sq_sqrt (show 0 ≤ 1-η by linarith)
  linear_combination -h+t*x (Fin.last (m+m))*hs

theorem actual_small_tail_schur (m : ℕ) (η t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/4) :
    nuclearLiftSmallest m η t = (1-η)*t-t^2*η*(1-η)*
      (nuclearUnitVector m ⬝ᵥ ((smallTailBlock m η t)⁻¹ *ᵥ nuclearUnitVector m)) := by
  let a := nuclearLiftSmallest m η t
  let H := nuclearLiftA_isHermitian m η t
  have hamem := nuclearLiftSmallest_mem m η t
  rw [H.spectrum_real_eq_range_eigenvalues] at hamem
  obtain ⟨j,hj⟩ := hamem
  let x : Fin (m+m+1) → ℝ := H.eigenvectorBasis j
  have hx : x ≠ 0 := by
    intro h
    have hz : H.eigenvectorBasis j = 0 := (WithLp.ofLp_eq_zero 2).mp h
    exact H.eigenvectorBasis.orthonormal.ne_zero j hz
  have he : nuclearLiftA m η t *ᵥ x = a • x := by
    simpa only [x,a,hj] using H.mulVec_eigenvectorBasis j
  let Q := smallTailBlock m η t
  let y : Fin (m+m) → ℝ := fun i => x i.castSucc
  let l := x (Fin.last (m+m))
  let c := t*Real.sqrt η*Real.sqrt (1-η)
  have hQ := (small_tail_block_posDef m η t hη0 hη1 ht0 ht1).isUnit
  have hp : Q *ᵥ y = (-(c*l)) • nuclearUnitVector m :=
    nuclear_eigenvector_prefix m η t a hη0 x he
  have hy : y = (-(c*l)) • (Q⁻¹ *ᵥ nuclearUnitVector m) := by
    have h := congrArg (fun v => Q⁻¹ *ᵥ v) hp
    rwa [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul Q (Matrix.isUnit_iff_isUnit_det Q |>.mp hQ),
      Matrix.one_mulVec,Matrix.mulVec_smul] at h
  have hl : l ≠ 0 := by
    intro hl
    have hy0 : y = 0 := by simpa only [hl,mul_zero,neg_zero,zero_smul] using hy
    apply hx
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · exact hl
    · exact congrFun hy0 k
  have hlast : a*l = c*(nuclearUnitVector m ⬝ᵥ y)+t*(1-η)*l :=
    nuclear_eigenvector_last m η t a hη1 x he
  rw [hy,dotProduct_smul] at hlast
  simp only [smul_eq_mul] at hlast
  have hc : c^2 = t^2*η*(1-η) := by
    dsimp [c]
    rw [mul_pow,mul_pow,Real.sq_sqrt hη0,Real.sq_sqrt (show 0 ≤ 1-η by linarith)]
  have hfactor : (a-((1-η)*t-t^2*η*(1-η)*
      (nuclearUnitVector m ⬝ᵥ (Q⁻¹ *ᵥ nuclearUnitVector m))))*l = 0 := by
    rw [← hc]
    linear_combination hlast
  exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hl)

#print axioms actual_small_tail_schur

end NLA.RA08.Paper.LiteralContour
