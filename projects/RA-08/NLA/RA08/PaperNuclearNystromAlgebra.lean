module

public import NLA.RA08.PaperNuclearNystromDefinitions
public import NLA.RA08.PaperNuclearFamily

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators
namespace NLA.RA08.Paper

theorem nuclearLiftSketch_injective (m : ℕ) (η : ℝ) :
    Function.Injective (fun x => nuclearLiftSketch m η *ᵥ x) := by
  intro x y h
  ext i
  have hi := congrFun h i.castSucc
  simpa [nuclearLiftSketch,Matrix.mulVec,dotProduct,Matrix.one_apply] using hi

theorem nuclearLiftVector_norm_sq (m : ℕ) (hm : 1 ≤ m) (η : ℝ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    ∑ i : Fin (m+m+1), (nuclearLiftVector m η i)^2=1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [nuclearLiftVector,Fin.snoc_castSucc,Fin.snoc_last,mul_pow,
    Real.sq_sqrt hη,Real.sq_sqrt (sub_nonneg.mpr hη1)]
  rw [← Finset.mul_sum,nuclearUnitVector_norm_sq m hm]
  ring

theorem nuclearLiftPerturbation_posSemidef (m : ℕ) (η : ℝ) :
    (nuclearLiftPerturbation m η).PosSemidef := by
  have he : nuclearLiftPerturbation m η=Matrix.vecMulVec (nuclearLiftVector m η)
      (star (nuclearLiftVector m η)) := by
    ext i j
    simp [nuclearLiftPerturbation,Matrix.vecMulVec]
  rw [he]
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem nuclearLiftA_isHermitian (m : ℕ) (η t : ℝ) :
    (nuclearLiftA m η t).IsHermitian := by
  have hB : (nuclearLiftBase m).IsHermitian := by
    simp [nuclearLiftBase,Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hB.add ((nuclearLiftPerturbation_posSemidef m η).isHermitian.smul (by simp [IsSelfAdjoint]))

theorem nuclearLiftPerturbation_sketch (m : ℕ) (η : ℝ) (hη : η < 1) :
    nuclearLiftPerturbation m η*nuclearLiftSketch m η=0 := by
  have hs : Real.sqrt (1-η) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  have hcol (j : Fin (m+m)) :
      (∑ k : Fin (m+m+1), nuclearLiftVector m η k*nuclearLiftSketch m η k j)=0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [nuclearLiftVector,nuclearLiftSketch,Fin.snoc_castSucc,Fin.snoc_last,Matrix.one_apply]
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    field_simp
    <;> ring
  ext i j
  simp only [Matrix.mul_apply,nuclearLiftPerturbation,Matrix.vecMulVec,Matrix.of_apply,Matrix.zero_apply,mul_assoc]
  rw [← Finset.mul_sum,hcol,mul_zero]

theorem nuclearLiftBase_sketch (m : ℕ) (η : ℝ) :
    nuclearLiftBase m*nuclearLiftSketch m η=nuclearLiftAOmega m := by
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [nuclearLiftBase,nuclearLiftBaseEntries,nuclearLiftSketch,nuclearLiftAOmega,Matrix.diagonal_mul]
  · by_cases hkj : k=j
    · subst j
      simp [nuclearLiftBase,nuclearLiftBaseEntries,nuclearLiftSketch,nuclearLiftAOmega,
        nuclearBase,Matrix.diagonal_mul,Matrix.diagonal_apply,Matrix.one_apply]
    · simp [nuclearLiftBase,nuclearLiftBaseEntries,nuclearLiftSketch,nuclearLiftAOmega,
        nuclearBase,Matrix.diagonal_mul,Matrix.diagonal_apply,Matrix.one_apply,hkj]

theorem nuclearLiftA_sketch (m : ℕ) (η t : ℝ) (hη : η < 1) :
    nuclearLiftA m η t*nuclearLiftSketch m η=nuclearLiftAOmega m := by
  rw [nuclearLiftA,Matrix.add_mul,Matrix.smul_mul,nuclearLiftPerturbation_sketch m η hη,
    smul_zero,add_zero,nuclearLiftBase_sketch]

theorem nuclearLiftSketch_gram (m : ℕ) (η t : ℝ) (hη : η < 1) :
    (nuclearLiftSketch m η).transpose*nuclearLiftA m η t*nuclearLiftSketch m η=nuclearBase m := by
  rw [Matrix.mul_assoc,nuclearLiftA_sketch m η t hη]
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_castSucc,
    nuclearLiftSketch,nuclearLiftAOmega,Fin.snoc_castSucc,Fin.snoc_last,Pi.zero_apply,mul_zero,add_zero]
  change ((1 : RealMatrix (m+m)).transpose*nuclearBase m) i j=(nuclearBase m) i j
  rw [Matrix.transpose_one,Matrix.one_mul]

theorem nuclearBaseInverse_mul (m : ℕ) : nuclearBaseInverse m*nuclearBase m=1 := by
  rw [nuclearBaseInverse,nuclearBase,Matrix.diagonal_mul_diagonal]
  have he : (fun i => (nuclearBaseEntries m i)⁻¹*nuclearBaseEntries m i)=fun _ => (1 : ℝ) := by
    funext i
    exact inv_mul_cancel₀ (ne_of_gt (nuclearBaseEntries_pos m i))
  rw [he,Matrix.diagonal_one]

theorem nuclearLift_nystrom (m : ℕ) (η t : ℝ) (hη : η < 1) :
    nystrom (nuclearLiftA m η t) (nuclearLiftSketch m η)=nuclearLiftBase m := by
  have ht : (nuclearLiftSketch m η).transpose*nuclearLiftA m η t=(nuclearLiftAOmega m).transpose := by
    have h := congrArg Matrix.transpose (nuclearLiftA_sketch m η t hη)
    have hs := (nuclearLiftA_isHermitian m η t).eq
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial] at hs
    simpa only [Matrix.transpose_mul,hs] using h
  rw [nystrom,nuclearLiftSketch_gram m η t hη,Matrix.inv_eq_left_inv (nuclearBaseInverse_mul m),
    nuclearLiftA_sketch m η t hη,Matrix.mul_assoc,ht]
  ext i j
  refine Fin.lastCases ?_ (fun p => ?_) i
  · simp [nuclearLiftAOmega,nuclearBaseInverse,Matrix.mul_apply,nuclearLiftBase,nuclearLiftBaseEntries,
      Matrix.diagonal_apply]
  · refine Fin.lastCases ?_ (fun q => ?_) j
    · simp [nuclearLiftAOmega,nuclearBaseInverse,Matrix.mul_apply,nuclearLiftBase,nuclearLiftBaseEntries,
        Matrix.diagonal_apply]
    · have hp := ne_of_gt (nuclearBaseEntries_pos m p)
      by_cases hpq : p=q
      · subst q
        simp [nuclearLiftAOmega,nuclearBaseInverse,nuclearBase,Matrix.mul_apply,nuclearLiftBase,
          nuclearLiftBaseEntries,Matrix.diagonal_apply,hp]
      · simp [nuclearLiftAOmega,nuclearBaseInverse,nuclearBase,Matrix.mul_apply,nuclearLiftBase,
          nuclearLiftBaseEntries,Matrix.diagonal_apply,hpq]

#print axioms nuclearLift_nystrom
end NLA.RA08.Paper
