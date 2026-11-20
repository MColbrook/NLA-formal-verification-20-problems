module

public import NLA.RA08.PaperNuclearTailQuadratic
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped Classical Matrix BigOperators MatrixOrder
namespace NLA.RA08.Paper

theorem nuclearLift_spectrum_nonempty (m : ℕ) (η t : ℝ) :
    (spectrum ℝ (nuclearLiftA m η t)).Nonempty :=
  ⟨_,(nuclearLiftA_isHermitian m η t).eigenvalues_mem_spectrum_real 0⟩

theorem nuclearLiftSmallest_mem (m : ℕ) (η t : ℝ) :
    nuclearLiftSmallest m η t ∈ spectrum ℝ (nuclearLiftA m η t) :=
  (Matrix.finite_real_spectrum (A := nuclearLiftA m η t)).isCompact.sInf_mem
    (nuclearLift_spectrum_nonempty m η t)

theorem nuclearLiftSmallest_le_spectrum (m : ℕ) (η t r : ℝ)
    (hr : r ∈ spectrum ℝ (nuclearLiftA m η t)) : nuclearLiftSmallest m η t ≤ r :=
  csInf_le (Matrix.finite_real_spectrum (A := nuclearLiftA m η t)).bddBelow hr

theorem nuclearLiftSmallest_pos (m : ℕ) (η t : ℝ) (hη : η < 1) (ht : 0 < t) :
    0 < nuclearLiftSmallest m η t := by
  have hA := nuclearLiftA_posDef m η t hη ht
  have hmem := nuclearLiftSmallest_mem m η t
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨i,hi⟩ := hmem
  rw [← hi]
  exact hA.eigenvalues_pos i

theorem nuclearLiftSmallest_sub_posSemidef (m : ℕ) (η t : ℝ) :
    (nuclearLiftA m η t-nuclearLiftSmallest m η t • 1).PosSemidef := by
  have hA := nuclearLiftA_isHermitian m η t
  have hn : 0 ≤ cfc (fun x : ℝ => x-nuclearLiftSmallest m η t)
      (nuclearLiftA m η t) :=
    cfc_nonneg (fun x hx => sub_nonneg.mpr (nuclearLiftSmallest_le_spectrum m η t x hx))
  have hid : cfc (fun x : ℝ => x) (nuclearLiftA m η t)=nuclearLiftA m η t :=
    cfc_id' ℝ _ hA
  have hconst : cfc (fun _ : ℝ => nuclearLiftSmallest m η t) (nuclearLiftA m η t)=
      nuclearLiftSmallest m η t • (1 : RealMatrix (m+m+1)) := by
    have hc : cfc (fun _ : ℝ => nuclearLiftSmallest m η t) (nuclearLiftA m η t)=
        algebraMap ℝ (RealMatrix (m+m+1)) (nuclearLiftSmallest m η t) :=
      cfc_const (nuclearLiftSmallest m η t) (nuclearLiftA m η t) hA
    simpa only [Algebra.algebraMap_eq_smul_one] using hc
  rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => nuclearLiftSmallest m η t)
    (nuclearLiftA m η t) continuous_id.continuousOn continuous_const.continuousOn,
    hid,hconst] at hn
  exact Matrix.nonneg_iff_posSemidef.mp hn

theorem nuclearLiftSmallest_upper (m : ℕ) (η t : ℝ) (hη : η ≤ 1) :
    nuclearLiftSmallest m η t ≤ (1-η)*t := by
  let x : Fin (m+m+1) → ℝ := Pi.single (Fin.last (m+m)) 1
  have h := (nuclearLiftSmallest_sub_posSemidef m η t).dotProduct_mulVec_nonneg x
  have hx : ∑ i : Fin (m+m+1), (x i)^2=1 := by
    simp [x,Pi.single_apply]
  have he : x ⬝ᵥ (nuclearLiftA m η t *ᵥ x)=(1-η)*t := by
    rw [nuclearLiftA_energy,nuclearLiftVector_dot]
    simp [x,dotProduct,Real.sq_sqrt (show 0 ≤ 1-η by linarith)]
    ring
  have hself : x ⬝ᵥ x=1 := by simpa only [dotProduct,← pow_two] using hx
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_sub,dotProduct_smul,smul_eq_mul,he,hself,mul_one] at h
  linarith

theorem nuclearLift_eigenvector_norm_sq (m : ℕ) (η t : ℝ) (i : Fin (m+m+1)) :
    ∑ j : Fin (m+m+1), ((nuclearLiftA_isHermitian m η t).eigenvectorBasis i j)^2=1 := by
  have hn := (nuclearLiftA_isHermitian m η t).eigenvectorBasis.norm_eq_one i
  have he := real_inner_self_eq_norm_sq
    ((nuclearLiftA_isHermitian m η t).eigenvectorBasis i)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at he
  simpa only [star_trivial,dotProduct,← pow_two,hn,one_pow] using he

theorem nuclearLiftSmallest_lower (m : ℕ) (hm : 1 ≤ m) (η t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1/4) :
    nuclearLiftTailLower η t ≤ nuclearLiftSmallest m η t := by
  have hA := nuclearLiftA_isHermitian m η t
  have hmem := nuclearLiftSmallest_mem m η t
  rw [hA.spectrum_real_eq_range_eigenvalues] at hmem
  obtain ⟨i,hi⟩ := hmem
  have h := nuclearLift_energy_lower m hm η t hη0 hη1 ht0 ht1 (hA.eigenvectorBasis i)
  rw [hA.mulVec_eigenvectorBasis,dotProduct_smul] at h
  have hn := nuclearLift_eigenvector_norm_sq m η t i
  have hd : (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (⇑(hA.eigenvectorBasis i))=1 := by
    simpa only [dotProduct,← pow_two] using hn
  rw [hn,hd] at h
  simpa only [smul_eq_mul,mul_one,hi] using h

#print axioms nuclearLiftSmallest_lower
end NLA.RA08.Paper
